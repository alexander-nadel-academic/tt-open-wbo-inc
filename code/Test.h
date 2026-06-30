/*!
 * \author Prateek Kumar - cs15btech11031@iith.ac.in
 *
 * @section LICENSE
 *
 * Open-WBO Copyright (c) 2018  Saurabh Joshi, Prateek Kumar, Sukrut Rao
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

#ifndef TEST_H
#define TEST_H

#include <random>
#include <algorithm>
#include <vector>

#include <iostream>
#include "encodings/Enc_GTECluster.h"
#include "encodings/Enc_GTEIncremental.h"

#define NUM_CLUSTERS 3
#define MAX_PER_CLUSTER 4
#define MAX_WEIGHT 10


/*_________________________________________________________________________________________________
  |
  |  test_encodig : (maxsat_formula : MaxSATFormula*, rhs1 : uint64_t, rhs2 : uint64_t, nsoft1 : int)
  |                 ->  [void]
  |
  |  Description:
  |
  |    This functions tests GTE Incremental by creating two trees and joining them.
  |    The clauses for both the trees are given in a file which is loaded by main
  |    function into maxsat_formula. The first nsoft soft clauses of maxsat_formula
  |    is used to create the first tree and remaining are used to create the second tree.
  |    The first tree has <= rhs1 constraint and second tree has <= rhs2 constraint.
  |    After joining, the RHS for AMK cnstraint is rhs2.
  |________________________________________________________________________________________________@*/
void test_encoding(MaxSATFormula *maxsat_formula, uint64_t rhs1, uint64_t rhs2, int nsoft1) {
	Solver *s = new Solver();

	vec<Lit> assumptions;
	vec<Lit> literals1;
	vec<uint64_t> weights_vec1;
	vec<Lit> literals2;
	vec<uint64_t> weights_vec2;

	for (int i=0; i<maxsat_formula->nSoft(); i++) {
		s->newVar();
		if (i<nsoft1) {
			literals1.push(maxsat_formula->getSoftClause(i).clause[0]);
			weights_vec1.push(maxsat_formula->getSoftClause(i).weight);
		} else {
			literals2.push(maxsat_formula->getSoftClause(i).clause[0]);
			weights_vec2.push(maxsat_formula->getSoftClause(i).weight);
		}
	}

	openwbo::GTEIncremental gte(_INCREMENTAL_ITERATIVE_);
	gte.encode(s, literals1, weights_vec1, rhs1);
	gte.update(s, rhs1, assumptions);
	gte.join(s, literals2, weights_vec2, rhs2, assumptions);
	gte.update(s, rhs2, assumptions);

	for (int i=0; i<maxsat_formula->nHard(); i++) {
		s->addClause(maxsat_formula->getHardClause(i).clause[0]);
	}

	bool solved = s->solve(assumptions);
	if (solved) {
		std::cout << "SAT" << std::endl;
	} else {
		std::cout << "UNSAT" << std::endl;
	}
	
	delete s;
}

/*_________________________________________________________________________________________________
  |
  |  test_encodig_join : [void] ->  [void]
  |
  |  Description:
  |
  |    This function randomly creates two GTE trees and joins them.
  |________________________________________________________________________________________________@*/
void test_encoding_join()
{
	std::random_device rd;
	std::mt19937 g(rd());
	std::uniform_int_distribution<unsigned int> dis(1, MAX_PER_CLUSTER);
	std::uniform_int_distribution<uint64_t> dis64(1, MAX_WEIGHT);

	// Generate random weights to be used by the trees
	std::vector<uint64_t> weights;
	for (int i=0; i<NUM_CLUSTERS; i++) {
		int n = dis(g);
		uint64_t w = dis64(g);
		for (int j=0; j<n; j++) {
			weights.push_back(w);
		}
	}

	Solver *s = new Solver();

	vec<Lit> literals1;
	vec<Lit> literals2;
	vec<uint64_t> weights_vec1;
	vec<uint64_t> weights_vec2;

	// Create literals and push into a vector
	std::vector<Lit> literals_vector;
	vec<uint64_t> weights_vec;
	for (unsigned i=0; i<weights.size(); i++) {
		literals_vector.push_back(mkLit(s->newVar(), false));
		weights_vec.push(weights[i]);
	}

	// Shuffle the literals
	std::shuffle(literals_vector.begin(), literals_vector.end(), g);

	std::uniform_int_distribution<unsigned> dis_tree2(0,1);

	for (unsigned i=0; i<literals_vector.size(); i++) {
		// Decide randomly whether to have the literal in first tree or second tree
		unsigned take_tree2 = dis_tree2(g);
		if (take_tree2) {
			literals2.push(literals_vector[i]);
			weights_vec2.push(weights_vec[i]);
		}
		else {
			literals1.push(literals_vector[i]);
			weights_vec1.push(weights_vec[i]);
		}
	}

	// Decide the number of unit clauses to be used as hard clauses and find the sum
	// of weights of those unit clauses
	std::uniform_int_distribution<unsigned> dis_unit(1, weights.size()/4+1);
	unsigned num_unit_clauses = dis_unit(g);

	uint64_t sum = 0;
	for (unsigned i=0; i<num_unit_clauses; i++) {
		sum += weights[i];
		s->addClause(literals_vector[i]);
	}

	openwbo::GTEIncremental gte(_INCREMENTAL_ITERATIVE_);
	vec<Lit> assumptions;
	uint64_t rhs = 0;
	std::uniform_int_distribution<unsigned> dis_rhs(0,1);
	unsigned unsat = dis_rhs(g); // Randomly decide whether formula should be SAT or UNSAT
	// Acoordingly randomly select RHS for atmost constraint for the final tree
	if (unsat) {
		std::uniform_int_distribution<unsigned> dis_rhs(0, sum-1);
		rhs = dis_rhs(g);
	} else {
		std::uniform_int_distribution<unsigned> dis_rhs(sum, 2*sum+1);
		rhs = dis_rhs(g);
	}

	// Randomly select RHS for the first tree
	std::uniform_int_distribution<unsigned> dis_rhs1(0, 2*sum+1);
	uint64_t rhs1 = dis_rhs1(g);

	std::cout << "Number of lits1: " << literals1.size() << std::endl
		<< "Number of lits2: " << literals2.size() << std::endl
	 	<< "Number of unit clauses: " << num_unit_clauses << std::endl;
	std::cout << "RHS1: " << rhs1 << std::endl;
	std::cout << "RHS: " << rhs << std::endl;

	// Encode using GTE and join the tree
	gte.encode(s, literals1, weights_vec1, rhs1);
	gte.update(s, rhs1, assumptions);
	gte.join(s, literals2, weights_vec2, rhs, assumptions);
	gte.update(s, rhs, assumptions);

	std::cout << "Encoded" << std::endl;

	// Solve the constraints
	bool solved = s->solve(assumptions);

	// Check if the answer was correct and print the case if test failed
	if (unsat) {
		if (solved) {
			std::cout << "TEST FAILED" << std::endl;
			std::cout << "SAT" << std::endl;
			std::cout << "c RHS1 " << rhs1 << std::endl;
			std::cout << "c RHS2 " << rhs << std::endl;
			std::cout << "c Nsoft " << weights_vec1.size() << std::endl;
			std::cout << "p wcnf " << weights_vec.size() << " " << weights_vec.size()+num_unit_clauses
				<< " " << MAX_WEIGHT+5 << std::endl;
			for (int i=0; i<weights_vec1.size(); i++) {
				std::cout << weights_vec1[i] << " " << i+1 << " 0" << std::endl;
			}
			for (int i=0; i<weights_vec2.size(); i++) {
				std::cout << weights_vec2[i] << " " << i+1 << " 0" << std::endl;
			}
			for (unsigned i=0; i<num_unit_clauses; i++) {
				std::cout << MAX_WEIGHT+5 << " " << i+1 << " 0" << std::endl;
			}
			std::cout << "c DONE" << std::endl;
		} else {
			std::cout << "UNSAT" << std::endl;
		}
	} else {
		if (solved) {
			std::cout << "SAT" << std::endl;
		} else {
			std::cout << "TEST FAILED" << std::endl;
			std::cout << "UNSAT" << std::endl;
			std::cout << "c RHS1 " << rhs1 << std::endl;
			std::cout << "c RHS2 " << rhs << std::endl;
			std::cout << "c Nsoft " << weights_vec1.size() << std::endl;
			std::cout << "p wcnf " << weights_vec.size() << " " << weights_vec.size()+num_unit_clauses
				<< " " << MAX_WEIGHT+5 << std::endl;
			for (int i=0; i<weights_vec1.size(); i++) {
				std::cout << weights_vec1[i] << " " << i+1 << " 0" << std::endl;
			}
			for (int i=0; i<weights_vec2.size(); i++) {
				std::cout << weights_vec2[i] << " " << i+1 << " 0" << std::endl;
			}
			for (unsigned i=0; i<num_unit_clauses; i++) {
				std::cout << MAX_WEIGHT+5 << " " << i+1 << " 0" << std::endl;
			}
			std::cout << "c DONE" << std::endl;
		}
	}

	delete s;
}

/*_________________________________________________________________________________________________
  |
  |  test_encodig : [maxsat_formula: MaxSATFormula*, rhs: uint64_t] ->  [void]
  |
  |  Description:
  |
  |    Test for GTE Incremental encoding for the given test case in a file
  |    which is loaded by main function in maxsat_formula.
  |________________________________________________________________________________________________@*/
void test_encoding(MaxSATFormula *maxsat_formula, uint64_t rhs) {
	Solver *s = new Solver();

	openwbo::GTEIncremental gte(_INCREMENTAL_ITERATIVE_);
	vec<Lit> assumptions;
	vec<Lit> literals;
	vec<uint64_t> weights_vec;

	for (int i=0; i<maxsat_formula->nSoft(); i++) {
		s->newVar();
		literals.push(maxsat_formula->getSoftClause(i).clause[0]);
		weights_vec.push(maxsat_formula->getSoftClause(i).weight);
	}

	gte.encode(s, literals, weights_vec, rhs);
	gte.update(s, rhs, assumptions);

	std::cout << "Encoded" << std::endl;

	for (int i=0; i<maxsat_formula->nHard(); i++) {
		s->addClause(maxsat_formula->getHardClause(i).clause[0]);
	}

	bool solved = s->solve(assumptions);
	if (solved) {
		std::cout << "SAT" << std::endl;
	} else {
		std::cout << "UNSAT" << std::endl;
	}
	
	delete s;
}

/*_________________________________________________________________________________________________
  |
  |  test_encodig : [void] ->  [void]
  |
  |  Description:
  |
  |    Randomly create a AMK constraint, encode using GTE and check SAT/UNSAT.
  |________________________________________________________________________________________________@*/
void test_encoding()
{
	std::random_device rd;
	std::mt19937 g(rd());
	std::uniform_int_distribution<unsigned int> dis(1, MAX_PER_CLUSTER);
	std::uniform_int_distribution<uint64_t> dis64(1, MAX_WEIGHT);

	// Create Random weights to be used for the soft clauses
	std::vector<uint64_t> weights;
	for (int i=0; i<NUM_CLUSTERS; i++) {
		int n = dis(g);
		uint64_t w = dis64(g);
		for (int j=0; j<n; j++) {
			weights.push_back(w);
		}
	}

	Solver *s = new Solver();

	std::vector<Lit> literals_vector;
	vec<Lit> literals;
	vec<uint64_t> weights_vec;

	// Get literals from the solvers
	for (unsigned i=0; i<weights.size(); i++) {
		literals_vector.push_back(mkLit(s->newVar(), false));
		weights_vec.push(weights[i]);
	}

	// Shuffle the literals
	std::shuffle(literals_vector.begin(), literals_vector.end(), g);

	for (unsigned i=0; i<literals_vector.size(); i++) {
		literals.push(literals_vector[i]);
	}

	// Decide number of unit clauses as hard clauses
	std::uniform_int_distribution<unsigned> dis_unit(1, weights.size()/4+1);
	unsigned num_unit_clauses = dis_unit(g);

	// Find the sum of weights of the unit hard clauses
	uint64_t sum = 0;
	for (unsigned i=0; i<num_unit_clauses; i++) {
		sum += weights[i];
		s->addClause(literals[i]);
	}

	openwbo::GTEIncremental gte(_INCREMENTAL_ITERATIVE_);
	vec<Lit> assumptions;
	uint64_t rhs = 0;
	std::uniform_int_distribution<unsigned> dis_rhs(0,1);
	// Randomly decide SAT/UNSAT and choose RHS of AMK constraint
	unsigned unsat = dis_rhs(g);
	if (unsat) {
		std::uniform_int_distribution<unsigned> dis_rhs(0, sum-1);
		rhs = dis_rhs(g);
	} else {
		std::uniform_int_distribution<unsigned> dis_rhs(sum, 2*sum+1);
		rhs = dis_rhs(g);
	}

	std::cout << "Number of lits: " << literals.size() << std::endl
	 	<< "Number of unit clauses: " << num_unit_clauses << std::endl;
	std::cout << "RHS: " << rhs << std::endl;
	// Encode the AMK constraint
	gte.encode(s, literals, weights_vec, rhs);
	
	// Randomly choose number of times to update the RHS
	std::uniform_int_distribution<unsigned> dis_num_inc(1, 100);
	unsigned num_inc = dis_num_inc(g);
	
	for (unsigned k=0; k < num_inc; k++) {
		std::cout << "RHS : " << rhs << std::endl;
		// Update RHS and solve
		gte.update(s, rhs, assumptions);

		std::cout << "Encoded" << std::endl;

		bool solved = s->solve(assumptions);

		// Check SAT/UNSAT and print the test case if failed

		if (unsat) {
			if (solved) {
				std::cout << "TEST FAILED" << std::endl;
				std::cout << "SAT" << std::endl;
				std::cout << "c RHS " << rhs << std::endl;
				std::cout << "p wcnf " << weights_vec.size() << " " << weights_vec.size()+num_unit_clauses
					<< " " << MAX_WEIGHT+5 << std::endl;
				for (int i=0; i<weights_vec.size(); i++) {
					std::cout << weights_vec[i] << " " << i+1 << " 0" << std::endl;
				}
				for (unsigned i=0; i<num_unit_clauses; i++) {
					std::cout << MAX_WEIGHT+5 << " " << i+1 << " 0" << std::endl;
				}
				std::cout << "c DONE" << std::endl;
			} else {
				std::cout << "UNSAT" << std::endl;
			}
		} else {
			if (solved) {
				std::cout << "SAT" << std::endl;
			} else {
				std::cout << "TEST FAILED" << std::endl;
				std::cout << "UNSAT" << std::endl;
				std::cout << "c RHS " << rhs << std::endl;
				std::cout << "p wcnf " << weights_vec.size() << " " << weights_vec.size()+num_unit_clauses
					<< " " << MAX_WEIGHT+5 << std::endl;
				for (int i=0; i<weights_vec.size(); i++) {
					std::cout << weights_vec[i] << " " << i+1 << " 0" << std::endl;
				}
				for (unsigned i=0; i<num_unit_clauses; i++) {
					std::cout << MAX_WEIGHT+5 << " " << i+1 << " 0" << std::endl;
				}
				std::cout << "c DONE" << std::endl;
			}
		}

		std::uniform_int_distribution<unsigned> dis_rhs(0,1);
		unsat = dis_rhs(g);
		if (unsat) {
			std::uniform_int_distribution<unsigned> dis_rhs(0, sum-1);
			rhs = dis_rhs(g);
		} else {
			std::uniform_int_distribution<unsigned> dis_rhs(sum, 2*sum+1);
			rhs = dis_rhs(g);
		}
	}
	
	delete s;
}

#endif
