/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.dss.decomposition

import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/** CPAchecker's hardcoded merge target (`DssDecompositionOptions.getConfiguredDecomposition`). */
const val DEFAULT_TARGET_BLOCK_COUNT = 2

/**
 * `MERGE_DECOMPOSITION` (CPAchecker's `MergeBlockNodesDecomposition`): [linearDecomposition], then
 * merging toward [targetBlockCount] (CPAchecker hardcodes 2). `mergeFunctionCalls` is not ported.
 */
class MergeBlockDecomposition(
  private val targetBlockCount: Int = DEFAULT_TARGET_BLOCK_COUNT,
  private val largestHorizontalMerge: Int = NO_MERGE_LIMIT,
  private val allowSingleBlockDecomposition: Boolean = false,
  private val linearDecomposition: DssBlockDecomposition = LinearBlockDecomposition(),
) : DssBlockDecomposition {

  override fun decompose(procedure: XcfaProcedure): BlockGraph {
    if (targetBlockCount <= 1 && allowSingleBlockDecomposition) {
      return SingleBlockDecomposition.decompose(procedure)
    }
    return mergeToTargetBlockCount(
      linearDecomposition.decompose(procedure),
      targetBlockCount,
      largestHorizontalMerge,
    )
  }
}
