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

package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.BooleanGlobalRelation
import hu.bme.mit.theta.analysis.algorithm.oc.GlobalRelation
import hu.bme.mit.theta.analysis.algorithm.oc.Reason
import hu.bme.mit.theta.analysis.algorithm.oc.Relation
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.solver.SolverStatus

internal class XcfaRefineryOcChecker : XcfaOcChecker {

  override val status: SolverStatus?
    get() = TODO("Not yet implemented") // run refinery on the problem, return SAT/UNSAT, null if not yet run

  override val model: Valuation?
    get() = TODO("Not yet implemented") // retrieve the model from refinery, if SAT, null otherwise

  override fun initialize(eg: XcfaToEventGraph.EventGraph) {
    TODO("Not yet implemented")
    // see XcfaSmtOcChecker for reference on what needs to be done in this initialization

    // build the refinery metamodel here
    // add property violation constraints, branching conditions
    // add event value assignment constraints
    // add rf-related constraints to the refinery problem here

    // do not add po and ws relation constraints here!
  }

  override fun addConflict(conflict: Reason) {
    // TODO add conflict to refinery problem, implement later...
  }

  override fun check(
    events: Map<VarDecl<*>, Map<Int, List<XcfaEvent>>>,
    pos: List<Relation<XcfaEvent>>,
    ppos: BooleanGlobalRelation,
    rfs: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>,
    wss: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>,
  ): SolverStatus? {
    TODO("Not yet implemented")
    // add po and ws relation constraints here
    // run refinery on the problem
  }

  override fun getHappensBefore(): GlobalRelation? {
    TODO("Not yet implemented")
    // retrieve all happens-before relations from the refinery solution, if SAT, null otherwise
  }

  override fun getPropagatedClauses(): List<Reason> = emptyList()

  override fun printStatistics(logger: Logger) {
    // TODO print refinery statistics, implement later...
  }
}
