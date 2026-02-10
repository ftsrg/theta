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
import tools.refinery.language.semantics.ModelInitializer
import tools.refinery.store.dse.modification.ModificationAdapter
import tools.refinery.store.dse.propagation.PropagationAdapter
import tools.refinery.store.dse.strategy.BestFirstStoreManager
import tools.refinery.store.dse.transition.DesignSpaceExplorationAdapter
import tools.refinery.store.dse.transition.DesignSpaceExplorationStoreAdapter
import tools.refinery.store.dse.transition.objectives.Criteria
import tools.refinery.store.model.ModelStore
import tools.refinery.store.query.ModelQueryAdapter
import tools.refinery.store.query.interpreter.QueryInterpreterAdapter
import tools.refinery.store.reasoning.ReasoningAdapter
import tools.refinery.store.reasoning.ReasoningStoreAdapter
import tools.refinery.store.statecoding.StateCoderAdapter
import tools.refinery.store.transition.system.TransitionSystemAdapter
import tools.refinery.store.transition.system.TransitionSystemBuilder
import tools.refinery.visualization.ModelVisualizerAdapter
import tools.refinery.visualization.internal.FileFormat
import kotlin.jvm.java

class RefineryChecker(
  private val transitionSystem: RefineryTransitionSystem,
  private val logger: Logger,
) : SafetyChecker<RefineryProof, Trace<ExplState, ExprAction>, UnitPrec> {

  override fun check(input: UnitPrec?): SafetyResult<RefineryProof, Trace<ExplState, ExprAction>> {
    val problem =
      StandaloneRefinery.getProblemLoader().loadString(transitionSystem.textualDeclarations)
    val initializer = StandaloneRefinery.getInstance(ModelInitializer::class.java)
    initializer.readProblem(problem)

    val storeBuilder =
      ModelStore.builder()
        .with(QueryInterpreterAdapter.builder())
        .with(
          ModelVisualizerAdapter.builder()
            .withOutputPath("test_output")
            .withFormat(FileFormat.SVG)
            .saveStates()
            .saveDesignSpace()
        )
        .with(PropagationAdapter.builder())
        .with(StateCoderAdapter.builder())
        .with(ModificationAdapter.builder())
        .with(TransitionSystemAdapter.builder())
        .with(ReasoningAdapter.builder())

    initializer.configureStoreBuilder(storeBuilder)

    val transitionSystemBuilder = storeBuilder.getAdapter(TransitionSystemBuilder::class.java)
    ProblemContext(initializer.problemTrace, storeBuilder).apply {
      transitionSystem.transitions.forEach { transition ->
        transitionSystemBuilder.transition(transition())
      }
      val targetProvider = transitionSystem.target
      transitionSystemBuilder.accept(Criteria.whenHasMatch(targetProvider()))
    }

    val store = storeBuilder.build()

    store.getAdapter(ReasoningStoreAdapter::class.java).createInitialModel(initializer.modelSeed).use { model ->
      val queryEngine = model.getAdapter(ModelQueryAdapter::class.java)
      val initialVersion = model.commit()
      queryEngine.flushChanges()

      val bestFirst = BestFirstStoreManager(store, 1)
      bestFirst.startExploration(initialVersion)
      model
        .getAdapter(ModelVisualizerAdapter::class.java)
        .visualize(bestFirst.getVisualizationStore())
    }

    TODO("Not yet implemented")
  }
}
