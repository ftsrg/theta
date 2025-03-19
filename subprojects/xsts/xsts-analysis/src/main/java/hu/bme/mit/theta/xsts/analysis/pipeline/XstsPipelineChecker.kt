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
package hu.bme.mit.theta.xsts.analysis.pipeline

import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MEPipelineCheckerConstructorArguments
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.formalisms.FormalismPipelineChecker
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import hu.bme.mit.theta.xsts.analysis.XstsToMonolithicAdapter

class XstsPipelineChecker<Pr : InvariantProof>(
  xsts: XSTS,
  pipelineArguments: MEPipelineCheckerConstructorArguments<Pr>,
) :
  FormalismPipelineChecker<XSTS, XstsState<out ExprState>, XstsAction, Pr, InvariantProof>(
    xsts,
    XstsToMonolithicAdapter(),
    pipelineArguments,
  )
