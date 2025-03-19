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
package hu.bme.mit.theta.sts.analysis.pipeline

import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MEPipelineCheckerConstructorArguments
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.formalisms.FormalismPipelineChecker
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.sts.STS
import hu.bme.mit.theta.sts.analysis.StsAction
import hu.bme.mit.theta.sts.analysis.StsToMonolithicAdapter

class StsPipelineChecker<Pr : InvariantProof>(
  sts: STS,
  pipelineArguments: MEPipelineCheckerConstructorArguments<Pr>,
) :
  FormalismPipelineChecker<STS, ExplState, StsAction, Pr, InvariantProof>(
    sts,
    StsToMonolithicAdapter(),
    pipelineArguments,
  )
