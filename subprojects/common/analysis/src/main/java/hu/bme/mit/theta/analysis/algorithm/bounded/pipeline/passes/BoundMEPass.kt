/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes

import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassResult
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPipelineCheckerStatus
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.PipelineDirection
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.exception.MEPassPipelineException

/** This pass throws an exception if the pipeline check has run more times than the given bound. */
class BoundMEPass<Pr : InvariantProof>(private val bound: Int) : MonolithicExprPass<Pr> {

  override fun process(
    data: MonolithicExprPassResult<Pr>,
    status: MonolithicExprPipelineCheckerStatus,
  ): MonolithicExprPassResult<Pr> {
    if (data.direction == PipelineDirection.FORWARD && status.checksRan >= bound) {
      throw BoundException(bound)
    }
    return data
  }

  class BoundException(bound: Int) :
    MEPassPipelineException("Pipeline check ran more times than $bound")
}
