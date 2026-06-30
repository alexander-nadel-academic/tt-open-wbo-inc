/*!
 * \author Sukrut Rao - cs15btech11036@iith.ac.in
 *
 * @section LICENSE
 *
 * Open-WBO, Copyright (c) 2018  Saurabh Joshi, Prateek Kumar, Sukrut Rao
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

#include "SequenceStatistic.h"

using namespace openwbo;

/*_________________________________________________________________________________________________
  |
  |  SequenceStatistic : (stat : Statistics)
  |
  |  Description:
  |
  |    Constructor for the class.
  |
  |  Pre-conditions:
  |    * None.
  |
  |  Post-conditions:
  |    * 'statistic' is set to 'stat'. Default is Mean.
  |
  |________________________________________________________________________________________________@*/
SequenceStatistic::SequenceStatistic(Statistics stat) { statistic = stat; }

/*_________________________________________________________________________________________________
  |
  |  setStatistic : (stat : Statistics) ->  [void]
  |
  |  Description:
  |
  |    Set the statistic to be used to 'stat'.
  |
  |  Pre-conditions:
  |    * None.
  |
  |  Post-conditions:
  |    * 'statistic' is set to 'stat'.
  |
  |________________________________________________________________________________________________@*/
void SequenceStatistic::setStatistic(Statistics stat) { statistic = stat; }

/*_________________________________________________________________________________________________
  |
  |  getSequenceStatistic : (sequence : vec<uint64_t> &) (start_index :
  |                         uint64_t) (end_index : uint64_t) ->  [uint64_t]
  |
  |  Description:
  |
  |    Get the value of the statistic 'statistic' for 'sequence' in the range of
  |    indices [start_index, end_index]
  |
  |  Pre-conditions:
  |    * 'start_index' must be less than or equal to 'end_index'.
  |    * 'start_index' and 'end_index' must be valid indices for 'sequence'.
  |    * 'sequence' must be sorted in ascending order.
  |
  |  Post-conditions:
  |    * 'sequence' is not modified.
  |
  |________________________________________________________________________________________________@*/
uint64_t SequenceStatistic::getSequenceStatistic(vec<uint64_t> &sequence,
                                                 uint64_t start_index,
                                                 uint64_t end_index) {
  if (start_index > end_index) {
    return 0;
  }
  switch (statistic) {
  case Statistics::_MEAN_:
    return meanStatistic(sequence, start_index, end_index);
    break;
  case Statistics::_MEDIAN_:
    return medianStatistic(sequence, start_index, end_index);
    break;
  case Statistics::_MAX_:
    return maxStatistic(sequence, start_index, end_index);
    break;
  case Statistics::_MIN_:
    return minStatistic(sequence, start_index, end_index);
    break;
  }
  return meanStatistic(sequence, start_index, end_index);
}

/*_________________________________________________________________________________________________
  |
  |  meanStatistic : (sequence : vec<uint64_t> &) (start_index :
  |                         uint64_t) (end_index : uint64_t) ->  [uint64_t]
  |
  |  Description:
  |
  |    Get the integer mean for 'sequence' in the range of indices
  |    [start_index, end_index]
  |
  |  Pre-conditions:
  |    * 'start_index' must be less than or equal to 'end_index'.
  |    * 'start_index' and 'end_index' must be valid indices for 'sequence'.
  |
  |  Post-conditions:
  |    * 'sequence' is not modified.
  |
  |________________________________________________________________________________________________@*/
uint64_t SequenceStatistic::meanStatistic(vec<uint64_t> &sequence,
                                          uint64_t start_index,
                                          uint64_t end_index) {

  uint64_t sum = 0;
  for (uint64_t i = start_index; i <= end_index; i++) {
    sum += sequence[i];
  }
  sum /= (end_index - start_index + 1);
  return sum;
}

/*_________________________________________________________________________________________________
  |
  |  medianStatistic : (sequence : vec<uint64_t> &) (start_index :
  |                         uint64_t) (end_index : uint64_t) ->  [uint64_t]
  |
  |  Description:
  |
  |    Get the median for 'sequence' in the range of indices
  |    [start_index, end_index]
  |
  |  Pre-conditions:
  |    * 'start_index' must be less than or equal to 'end_index'.
  |    * 'start_index' and 'end_index' must be valid indices for 'sequence'.
  |    * 'sequence' must be sorted in ascending order.
  |
  |  Post-conditions:
  |    * 'sequence' is not modified.
  |    * When the length of 'sequence' is even, the right side median is
  |      returned.
  |
  |________________________________________________________________________________________________@*/
uint64_t SequenceStatistic::medianStatistic(vec<uint64_t> &sequence,
                                            uint64_t start_index,
                                            uint64_t end_index) {

  uint64_t index = (start_index + end_index + 1) / 2;
  return sequence[index];
}

/*_________________________________________________________________________________________________
  |
  |  maxStatistic : (sequence : vec<uint64_t> &) (start_index :
  |                         uint64_t) (end_index : uint64_t) ->  [uint64_t]
  |
  |  Description:
  |
  |    Get the maximum value in. 'sequence' in the range of indices
  |    [start_index, end_index]
  |
  |  Pre-conditions:
  |    * 'start_index' must be less than or equal to 'end_index'.
  |    * 'start_index' and 'end_index' must be valid indices for 'sequence'.
  |    * 'sequence' must be sorted in ascending order.
  |
  |  Post-conditions:
  |    * 'sequence' is not modified.
  |
  |________________________________________________________________________________________________@*/
uint64_t SequenceStatistic::maxStatistic(vec<uint64_t> &sequence,
                                         uint64_t start_index,
                                         uint64_t end_index) {

  return sequence[end_index];
}

/*_________________________________________________________________________________________________
  |
  |  minStatistic : (sequence : vec<uint64_t> &) (start_index :
  |                         uint64_t) (end_index : uint64_t) ->  [uint64_t]
  |
  |  Description:
  |
  |    Get the minimum value in. 'sequence' in the range of indices
  |    [start_index, end_index]
  |
  |  Pre-conditions:
  |    * 'start_index' must be less than or equal to 'end_index'.
  |    * 'start_index' and 'end_index' must be valid indices for 'sequence'.
  |    * 'sequence' must be sorted in ascending order.
  |
  |  Post-conditions:
  |    * 'sequence' is not modified.
  |
  |________________________________________________________________________________________________@*/
uint64_t SequenceStatistic::minStatistic(vec<uint64_t> &sequence,
                                         uint64_t start_index,
                                         uint64_t end_index) {

  return sequence[start_index];
}
