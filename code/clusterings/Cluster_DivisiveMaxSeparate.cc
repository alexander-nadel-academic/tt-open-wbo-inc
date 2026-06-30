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

#include "Cluster_DivisiveMaxSeparate.h"

using namespace openwbo;

/*_________________________________________________________________________________________________
  |
  |  Cluster_DivisiveMaxSeparate : (formula : MaxSATFormulaExtended *)
  |                                (cluster_stat : Statisticss)
  |
  |  Description:
  |
  |    Constructor for the class.
  |
  |  Pre-conditions:
  |    * 'formula' must not be NULL.
  |
  |  Post-conditions:
  |    * Weights in 'formula' are sorted in ascending order.
  |    * Weights in 'formula' are stored in 'original_weights' in ascending
  |      order.
  |    * 'cluster_stat' is stored in 'cluster_statistic'.
  |    * Statistic is set in 'statistic_finder'.
  |    * 'max_c' is set to '1'. 'cluster_indices' contains {0,false}.
  |    * 'distances' contains the differences of weights in 'formula' when
  |      sorted in ascending order.
  |
  |________________________________________________________________________________________________@*/
Cluster_DivisiveMaxSeparate::Cluster_DivisiveMaxSeparate(
    MaxSATFormulaExtended *formula, Statistics cluster_statistic)
    : Cluster(formula, cluster_statistic) {
  // by default, set 'max_c' to one cluster, and set 'cluster_indices'
  // appropriately. No extra information is need to create a single cluster
  max_c = 1;
  cluster_indices.push({0, false});
  distances.growTo(original_weights.size() - 1);
  // store distances between weights
  for (int64_t i = 0; i < (int64_t)original_weights.size() - 1; ++i) {
    distances[i] = original_weights[i + 1] - original_weights[i];
  }
}

/*_________________________________________________________________________________________________
  |
  |  clusterWeights : (formula : MaxSATFormulaExtended *) (c : uint64_t) ->
  |                   [void]
  |
  |  Description:
  |
  |    Performs divisive clustering over the weights of 'formula' to create 'c'
  |    clusters. It starts off with all weights as a single cluster. Then,
  |    iteratively, the algorithm splits out new clusters at the point where the
  |    distance between consecutive weights inside some cluster is the highest.
  |    This is done until 'c' clusters are created. The number of clusters
  |    created so far is stored in 'max_c', so that the algorithm can continue
  |    from that point if the number of clusters are to be incremented at a
  |    later stage (assuming 'formula' is the same).
  |
  |  Pre-conditions:
  |    * 'formula' must be the same as that passed to the constructor.
  |
  |  Post-conditions:
  |    * Weights in 'formula' are replaced with clustered weights.
  |    * 'max_c' is set to be 'c'.
  |    * If 'c' is 0, then a single cluster is created.
  |    * If 'c' is more than the number of weights,
  |
  |________________________________________________________________________________________________@*/
void Cluster_DivisiveMaxSeparate::clusterWeights(MaxSATFormulaExtended *formula,
                                                 uint64_t c) {
  // if the number of clusters is more than the number of weights, truncate it
  // to the number of weights
  if (c > (uint64_t)original_weights.size()) {
    printf("c Limiting number of clusters to number of weights\n");
    c = original_weights.size();
    // weights will be the same as the original weights. This assumes that all
    // statistics keep the weight intact if a singleton set of weights is
    // passed.

    // FIXME: is this suppose to be here? was not here in the previous version!
    restoreWeights(formula); // TODO - check this!
    return;
  }

  // if cluster indices for 'c' clusters are already available, use them
  // directly
  if (c == max_c) {
    replaceWeights(formula, cluster_indices);
  } else {
    vec<cluster_index> temp;

    // if 'c' is less than 'max_c', clustering needs to start afresh from '1',
    // as the cluster configuration for intermediate steps is not stored
    if (c < max_c) {
      max_c = 1;
      cluster_indices.clear();
      cluster_indices.push({0, false});
    }

    // bounds for existing clusters
    uint64_t low_index, high_index;
    // distance and index of point where next split will occur
    uint64_t max_distance, max_index;
    // whether weights in a cluster are known to be not all equal
    bool intra_nonzero;

    // iteratively create clusters
    for (uint64_t i = max_c; i < c; i++) {
      temp.clear();
      max_distance = 0;
      max_index = 0;

      // iterate over existing clusters to find the point of next split
      for (uint64_t j = 0; j < (uint64_t)cluster_indices.size(); j++) {
        // if all weights in a cluster are known to be identical, do not
        // iterate, as the max distance is known to be zero
        if (cluster_indices[j].all_equal_in_cluster) {
          continue;
        }
        low_index = cluster_indices[j].index;
        high_index = (j == (uint64_t)cluster_indices.size() - 1
                          ? original_weights.size() - 1
                          : cluster_indices[j + 1].index - 1);
        intra_nonzero = false;

        // find max distance in this cluster, and compare with and set
        // 'max_distance' and 'max_index' as applicable
        for (uint64_t k = low_index; k < high_index; k++) {
          if (distances[k] > max_distance) {
            max_distance = distances[k];
            max_index = k + 1;
          }

          // check if there exist some weights that are unequal in this cluster
          if (distances[k] > 0) {
            intra_nonzero = true;
          }
        }

        // if all weights in this cluster are known to be equal, set attribute
        // so that unnecessary iterations can be avoided
        if (!intra_nonzero) {
          cluster_indices[j].all_equal_in_cluster = true;
        }
      }

      // stop if all weights within all clusters are known to be equal.
      // clustering from this point onwards will not change the weights in any
      // way
      if (max_distance == 0) {
        printf("c Redundant split found\n");
        break;
      }

      // add newly found index to 'cluster_indices'
      bool is_added = false;
      for (uint64_t j = 0; j < (uint64_t)cluster_indices.size(); j++) {
        if (cluster_indices[j].index > max_index && !is_added) {
          temp.push({max_index, false});
          is_added = true;
        }
        temp.push(cluster_indices[j]);
      }
      if (max_index >= cluster_indices[cluster_indices.size() - 1].index) {
        temp.push({max_index, false});
      }
      temp.copyTo(cluster_indices);
    }

    // replace weights after finding all indices
    replaceWeights(formula, cluster_indices);
    max_c = c;
  }
}
