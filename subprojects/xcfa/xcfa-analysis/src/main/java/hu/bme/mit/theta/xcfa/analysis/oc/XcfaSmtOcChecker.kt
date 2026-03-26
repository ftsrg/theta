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

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.solver.SolverStatus

internal open class XcfaSmtOcChecker(protected val ocChecker: SmtOcChecker<E>) :
  SmtOcChecker<E>(), XcfaOcChecker {

  override val solver
    get() = ocChecker.solver

  override val status: SolverStatus?
    get() = solver.status

  override val model: Valuation?
    get() = solver.model

  override fun initialize(eg: XcfaToEventGraph.EventGraph) {
    // Value assignment
    eg.events.values
      .flatMap { it.values.flatten() }
      .filter { it.assignment != null }
      .forEach { event ->
        if (event.guard.isEmpty()) solver.add(event.assignment)
        else solver.add(Imply(event.guardExpr, event.assignment))
      }

    // Branching conditions
    eg.branchingConditions.forEach { solver.add(it) }

    // Property violation
    solver.add(Or(eg.violations.map { it.guard }))

    // RF
    eg.rfs.forEach { (v, list) ->
      list
        .groupBy { it.to }
        .forEach { (event, rels) ->
          rels.forEach { rel ->
            var conseq = And(rel.from.guardExpr, rel.to.guardExpr)
            if (rel.from.const != eg.memoryGarbage) {
              conseq = And(conseq, Eq(rel.from.const.ref, rel.to.const.ref))
              if (v == eg.memoryDecl) {
                conseq =
                  And(conseq, Eq(rel.from.array, rel.to.array), Eq(rel.from.offset, rel.to.offset))
              }
            }
            solver.add(Imply(rel.declRef, conseq)) // RF-Val
          }
          solver.add(Imply(event.guardExpr, Or(rels.map { it.declRef }))) // RF-Some
        }
    }
  }

  override fun addConflict(conflict: Reason) = solver.add(Not(conflict.expr))

  override fun check(
    events: Map<VarDecl<*>, Map<Int, List<XcfaEvent>>>,
    pos: List<Relation<XcfaEvent>>,
    ppos: BooleanGlobalRelation,
    rfs: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>,
    wss: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>,
  ): SolverStatus? = ocChecker.check(events, pos, ppos, rfs, wss)

  override fun getHappensBefore(): GlobalRelation? = ocChecker.getHappensBefore()

  override fun getPropagatedClauses(): List<Reason> = ocChecker.getPropagatedClauses()

  override fun printStatistics(logger: Logger) {
    solver.statistics.let {
      logger.info("Solver statistics:")
      it.forEach { (k, v) -> logger.info("$k: $v") }
    }
  }
}
