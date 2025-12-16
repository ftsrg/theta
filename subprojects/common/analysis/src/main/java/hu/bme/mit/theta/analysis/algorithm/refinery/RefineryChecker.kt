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
package hu.bme.mit.theta.analysis.algorithm.refinery

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import tools.refinery.generator.standalone.StandaloneRefinery
import tools.refinery.store.dse.transition.DesignSpaceExplorationAdapter

class RefineryChecker(private val transitionSystem: String, private val logger: Logger) :
  SafetyChecker<RefineryProof, Trace<ExplState, ExprAction>, UnitPrec> {

  override fun check(input: UnitPrec?): SafetyResult<RefineryProof, Trace<ExplState, ExprAction>> {
    val problem = StandaloneRefinery.getProblemLoader().loadString(transitionSystem)
    val generator = StandaloneRefinery.getGeneratorFactory().createGenerator(problem)
    val model = generator.model

    val adapter = model.getAdapter(DesignSpaceExplorationAdapter::class.java)
    adapter.transformations.forEach { System.err.println(it) }

    TODO("Not yet implemented")
  }
}
