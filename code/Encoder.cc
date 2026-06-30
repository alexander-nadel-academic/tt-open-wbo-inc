/*!
 * \author Ruben Martins - ruben@sat.inesc-id.pt
 *
 * @section LICENSE
 *
 * Open-WBO, Copyright (c) 2013-2017, Ruben Martins, Vasco Manquinho, Ines Lynce
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */

#include "Encoder.h"

using namespace openwbo;

/************************************************************************************************
 //
 // Encoding of exactly-one constraints
 //
 ************************************************************************************************/
void Encoder::encodeAMO(Solver *S, vec<Lit> &lits) {
  vec<Lit> lits_copy;
  lits.copyTo(lits_copy);

  switch (amo_encoding) {
  // Currently only the ladder encoding is used for AMO constraints.
  case _AMO_LADDER_:
    ladder.encode(S, lits_copy);
    break;

  default:
    printf("Error: Invalid at-most-one encoding.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

/************************************************************************************************
 //
 // Encoding of cardinality constraints
 //
 ************************************************************************************************/

int Encoder::predictCardinality(Solver *S, vec<Lit> &lits, uint64_t rhs, int maxVal)
 {
	 const int64_t approxVal = (int64_t)2 * (int64_t)lits.size() * rhs;
	if (approxVal > (int64_t)INT_MAX || approxVal < (int64_t)rhs)
	{
		return INT_MAX;
	}
	
	return (int)approxVal;
	
  /*switch (cardinality_encoding) {
  case _CARD_MTOTALIZER_:
    return mtotalizer.predict(S, lits, rhs, maxVal);    

  case _CARD_CNETWORKS_:
  case _CARD_TOTALIZER_:
    return -1;    

  default:
    printf("Error: Invalid cardinality encoding.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }*/
 }
  
//
// Manages the encoding of cardinality encodings.
void Encoder::encodeCardinality(Solver *S, vec<Lit> &lits, int64_t rhs) {
  vec<Lit> lits_copy;
  lits.copyTo(lits_copy);

  switch (cardinality_encoding) {
  case _CARD_TOTALIZER_:
    printf("c encodeCardinality : CARD_TOTALIZER_\n");
    totalizer.build(S, lits_copy, rhs);
    if (totalizer.hasCreatedEncoding())
      totalizer.update(S, rhs);
    break;

  case _CARD_MTOTALIZER_:
    printf("c encodeCardinality : CARD_MTOTALIZER_\n");
    mtotalizer.encode(S, lits_copy, rhs);
    break;

  case _CARD_CNETWORKS_:
    printf("c encodeCardinality : _CARD_CNETWORKS_\n");
    cnetworks.encode(S, lits_copy, rhs);
    break;

  default:
    printf("Error: Invalid cardinality encoding.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

void Encoder::addCardinality(Solver *S, Encoder &enc, int64_t rhs) {
  if (cardinality_encoding == _CARD_TOTALIZER_ &&
      enc.cardinality_encoding == _CARD_TOTALIZER_) {
    totalizer.add(S, enc.totalizer, rhs);
  } else {
    printf("Error: Cardinality encoding does not support incrementality.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

// Manages the update of cardinality constraints.
void Encoder::updateCardinality(Solver *S, int64_t rhs) {

  switch (cardinality_encoding) {
  case _CARD_TOTALIZER_:
    totalizer.update(S, rhs);
    break;

  case _CARD_MTOTALIZER_:
    mtotalizer.update(S, rhs);
    break;

  case _CARD_CNETWORKS_:
    cnetworks.update(S, rhs);
    break;

  default:
    printf("Error: Invalid cardinality encoding.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

// Incremental methods for cardinality encodings:
//
// Manages the building of cardinality encodings.
// Currently is only used for incremental solving.
void Encoder::buildCardinality(Solver *S, vec<Lit> &lits, int64_t rhs) {
  assert(incremental_strategy != _INCREMENTAL_NONE_);

  vec<Lit> lits_copy;
  lits.copyTo(lits_copy);

  switch (cardinality_encoding) {
  case _CARD_TOTALIZER_:
    totalizer.build(S, lits_copy, rhs);
    break;

  default:
    printf("Error: Cardinality encoding does not support incrementality.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

// Manages the incremental update of cardinality constraints.
void Encoder::incUpdateCardinality(Solver *S, vec<Lit> &join, vec<Lit> &lits,
                                   int64_t rhs, vec<Lit> &assumptions) {
  assert(incremental_strategy == _INCREMENTAL_ITERATIVE_ ||
         incremental_strategy == _INCREMENTAL_WEAKENING_);

  vec<Lit> join_copy;
  join.copyTo(join_copy);
  vec<Lit> lits_copy;
  lits.copyTo(lits_copy);
  // Note: the assumption vector will be updated in this procedure

  switch (cardinality_encoding) {
  case _CARD_TOTALIZER_:
    if (join.size() > 0)
      totalizer.join(S, join_copy, rhs);

    assert(lits.size() > 0);
    totalizer.update(S, rhs, lits_copy, assumptions);
    break;

  default:
    printf("Error: Cardinality encoding does not support incrementality.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

void Encoder::joinEncoding(Solver *S, vec<Lit> &lits, int64_t rhs) {

  switch (cardinality_encoding) {
  case _CARD_TOTALIZER_:
    totalizer.join(S, lits, rhs);
    break;

  default:
    printf("Error: Cardinality encoding does not support incrementality.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

/************************************************************************************************
 //
 // Encoding of pseudo-Boolean constraints
 //
 ************************************************************************************************/
//
// Manages the encoding of PB encodings.
void Encoder::encodePB(Solver *S, vec<Lit> &lits, vec<uint64_t> &coeffs,
                       uint64_t rhs) {

  vec<Lit> lits_copy;
  lits.copyTo(lits_copy);
  vec<uint64_t> coeffs_copy;
  coeffs.copyTo(coeffs_copy);

  switch (pb_encoding) {
  case _PB_SWC_:
    swc.encode(S, lits_copy, coeffs_copy, rhs);
    break;

  case _PB_GTE_:
    gte.encode(S, lits_copy, coeffs_copy, rhs);
    break;

  case _PB_GTECLUSTER_:
    gtecluster.encode(S, lits_copy, coeffs_copy, rhs);
    break;

  case _PB_ADDER_:
    adder.encode(S, lits_copy, coeffs_copy, rhs);
    break;

  default:
    printf("Error: Invalid PB encoding.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

int Encoder::predictPB(Solver *S, vec<Lit> &lits, vec<uint64_t> &coeffs,
                       uint64_t rhs) {

  vec<Lit> lits_copy;
  lits.copyTo(lits_copy);
  vec<uint64_t> coeffs_copy;
  coeffs.copyTo(coeffs_copy);

  switch (pb_encoding) {
  case _PB_SWC_:
    return -1;
    break;

  case _PB_GTE_:
    return gte.predict(S, lits_copy, coeffs_copy, rhs);
    break;

  case _PB_GTECLUSTER_:
    return -1;
    break;

  case _PB_ADDER_:
    return -1;
    break;

  default:
    printf("Error: Invalid PB encoding.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

// Manages the update of PB encodings.
void Encoder::updatePB(Solver *S, uint64_t rhs) {

  switch (pb_encoding) {
  case _PB_SWC_:
    swc.update(S, rhs);
    break;

  case _PB_GTE_:
    gte.update(S, rhs);
    break;

  case _PB_GTECLUSTER_:
    gtecluster.update(S, rhs);
    break;

  case _PB_ADDER_:
    adder.update(S, rhs);
    break;

  default:
    printf("Error: Invalid PB encoding.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

// Incremental methods for PB encodings:
//
// Manages the incremental encode of PB encodings.
// Sukrut - encode, but assumptions come from outside 
// why don't PB encodings store them inside like totalizer? TODO
void Encoder::incEncodePB(Solver *S, vec<Lit> &lits, vec<uint64_t> &coeffs,
                          int64_t rhs, vec<Lit> &assumptions, int size) {
  assert(incremental_strategy == _INCREMENTAL_ITERATIVE_);

  vec<Lit> lits_copy;
  lits.copyTo(lits_copy);
  vec<uint64_t> coeffs_copy;
  coeffs.copyTo(coeffs_copy);
  // Note: the assumption vector will be updated in this procedure

  switch (pb_encoding) {
    // case _PB_GTE_:
    //   gte.encodeInc(S, lits_copy, coeffs_copy, rhs, assumptions);
    //   break;

  case _PB_SWC_:
    swc.encode(S, lits_copy, coeffs_copy, rhs, assumptions, size);
    break;
    
  // case _PB_GTE_INC_:
  // 	gteinc.encode(S, lits_copy, coeffs_copy, rhs);
  // 	gteinc.update(S, rhs, assumptions);
  //   break;

  // case _PB_ADDER_:
  //   adder.encodeInc(S, lits_copy, coeffs_copy, rhs, assumptions);
  //   break;

  default:
    printf("Error: PB encoding does not support incrementality.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

// Manages the incremental update of PB encodings.
void Encoder::incUpdatePB(Solver *S, vec<Lit> &lits, vec<uint64_t> &coeffs,
                          int64_t rhs, vec<Lit> &assumptions) {
  assert(incremental_strategy == _INCREMENTAL_ITERATIVE_);

  vec<Lit> lits_copy;
  lits.copyTo(lits_copy);
  vec<uint64_t> coeffs_copy;
  coeffs.copyTo(coeffs_copy);
  // Note: the assumption vector will be updated in this procedure

  switch (pb_encoding) {
  // case _PB_GTE_:
  //   gte.updateInc(S, rhs, assumptions);
  //   break;

  case _PB_SWC_:
    swc.update(S, rhs, assumptions);
    swc.join(S, lits_copy, coeffs_copy, assumptions);
    break;
    
  // case _PB_GTE_INC_:
  // 	gteinc.join(S, lits_copy, coeffs_copy, rhs, assumptions);
  // 	gteinc.update(S, rhs, assumptions);
  //   break;

  // case _PB_ADDER_:
  //   adder.updateInc(S, rhs, assumptions);
  //   break;

  default:
    printf("Error: PB encoding does not support incrementality.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

// Manages the incremental update of assumptions.
// Currently only used for the iterative encoding with SWC.
void Encoder::incUpdatePBAssumptions(Solver *S, vec<Lit> &assumptions) {
  assert(incremental_strategy == _INCREMENTAL_ITERATIVE_);

  switch (pb_encoding) {
  case _PB_SWC_:
    swc.updateAssumptions(S, assumptions);
    break;

  default:
    printf("Error: PB encoding does not support incrementality.\n");
    printf("s UNKNOWN\n");
    exit(_ERROR_);
  }
}

vec<Lit> &Encoder::lits() {
  assert(cardinality_encoding == _CARD_TOTALIZER_ &&
         incremental_strategy == _INCREMENTAL_ITERATIVE_);

  return totalizer.lits();
}

vec<Lit> &Encoder::outputs() {
  assert(cardinality_encoding == _CARD_TOTALIZER_ &&
         incremental_strategy == _INCREMENTAL_ITERATIVE_);

  return totalizer.outputs();
}

/************************************************************************************************
 //
 // Other
 //
 ************************************************************************************************/
// Returns true if the cardinality encoding was built, false otherwise.
bool Encoder::hasCardEncoding() {

  if (cardinality_encoding == _CARD_TOTALIZER_)
    return totalizer.hasCreatedEncoding();
  else if (cardinality_encoding == _CARD_MTOTALIZER_)
    return mtotalizer.hasCreatedEncoding();
  else if (cardinality_encoding == _CARD_CNETWORKS_)
    return cnetworks.hasCreatedEncoding();

  return false;
}

// Returns true if the PB encoding was built, false otherwise.
bool Encoder::hasPBEncoding() {
  if (pb_encoding == _PB_SWC_)
    return swc.hasCreatedEncoding();
  else if (pb_encoding == _PB_GTE_)
    return gte.hasCreatedEncoding();
  else if (pb_encoding == _PB_GTECLUSTER_)
    return gtecluster.hasCreatedEncoding();
  else if (pb_encoding == _PB_GTE_INC_)
    return gteinc.hasCreatedEncoding();
  else if (pb_encoding == _PB_ADDER_)
    return adder.hasCreatedEncoding(); 
  return false;
}
