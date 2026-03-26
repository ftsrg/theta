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
package hu.bme.mit.theta.analysis.algorithm.oc

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.solver.SolverStatus

/**
 * This is an interface of an ordering consistency checker for concurrent systems (e.g., concurrent
 * programs).
 *
 * An ordering consistency checker takes a set an events and a set of relation between events. It
 * checks whether there is an inconsistency (a cycle in the event graph based on the relations)
 * subject to the constraints added to the SMT-solver.
 */
interface OcChecker<E : Event> {

  /**
   * Checks the consistency of the event graph (i.e., if there is a partial order of events
   * satisfying the given constraints).
   *
   * @param events the set of events grouped by variables
   * @param pos the elements of the program order relation
   * @param ppos preserved program order relation (as a matrix with indices as clkIds)
   * @param rfs the (possible) elements of the "read-from" relation (not all of these are
   *   necessarily enabled)
   * @return returns the status of the solver after running the consistency checking
   */
  fun check(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    pos: List<Relation<E>>,
    ppos: BooleanGlobalRelation,
    rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ): SolverStatus?

  /**
   * Get the discovered relations represented by their reasons between the events (or more exactly
   * between atomic blocks, see Event::clkId). You may index the relation by clkIds:
   * ```
   * val relation = checker.getHappensBefore()
   * val reason = relation[clkId1, clkId2]
   * ```
   */
  fun getHappensBefore(): GlobalRelation?

  /**
   * Get the list of propagated conflict clauses (their negations were added to the solver) in the
   * form of reasons.
   */
  fun getPropagatedClauses(): List<Reason>
}
