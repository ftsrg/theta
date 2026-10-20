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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus
import hu.bme.mit.theta.analysis.expr.refinement.VarsRefutation
import hu.bme.mit.theta.core.utils.IndexedVars
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory

/**
 * Re-indexes the refutations of this checker from SSA indices to trace positions: a variable
 * version goes to the first state at which the variable has reached that version.
 *
 * [XcfaPrecRefiner] maps variables back through the lookup of the state at each index, and pruning
 * uses the index as a node position; both need positions, which SSA indices are not once procedure
 * instances or multi-statement edges are involved.
 */
fun ExprTraceChecker<VarsRefutation>.withTracePositionIndices(): ExprTraceChecker<VarsRefutation> {
  val checker = this
  return object : ExprTraceChecker<VarsRefutation> {
    override fun check(
      trace: Trace<out ExprState, out ExprAction>
    ): ExprTraceStatus<VarsRefutation> {
      val status = checker.check(trace)
      if (status.isFeasible) return status
      val varSets = status.asInfeasible().refutation.varSets
      val indexings =
        trace.actions.runningFold(VarIndexingFactory.indexing(0)) { indexing, action ->
          indexing.add(action.nextIndexing())
        }
      val builder = IndexedVars.builder()
      for (ssaIndex in varSets.nonEmptyIndexes) {
        for (varDecl in varSets.getVars(ssaIndex)) {
          val position = indexings.indexOfFirst { it.get(varDecl) >= ssaIndex }
          builder.add(if (position < 0) indexings.lastIndex else position, varDecl)
        }
      }
      return ExprTraceStatus.infeasible(VarsRefutation.create(builder.build()))
    }

    override fun toString(): String = checker.toString()
  }
}
