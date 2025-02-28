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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverStatus
import java.io.File
import kotlin.time.measureTime

internal class XcfaOcCorrectnessValidator(
  private val ocChecker: OcChecker<E>,
  private val inputConflictClauseFile: String,
  private val permissive: Boolean = true,
  private val logger: Logger,
) : OcChecker<E> {

  private var clauseValidationTime = 0L
  private lateinit var nonOcSolver: Solver
  private lateinit var ppos: BooleanGlobalRelation

  init {
    if (!permissive) {
      nonOcSolver = SolverManager.resolveSolverFactory("Z3:4.13").createSolver()
    }
  }

  override val solver
    get() = if (permissive) ocChecker.solver else nonOcSolver

  override fun getHappensBefore() = if (permissive) ocChecker.getHappensBefore() else null

  override fun getPropagatedClauses(): List<Reason> =
    if (permissive) ocChecker.getPropagatedClauses() else listOf()

  override fun check(
      events: Map<VarDecl<*>, Map<Int, List<E>>>,
      pos: List<Relation<E>>,
      ppos: BooleanGlobalRelation,
      rfs: Map<VarDecl<*>, Set<Relation<E>>>,
      wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ): SolverStatus? {
    val flatRfs = rfs.values.flatten()
    val flatWss = wss.values.flatten()
    val flatEvents = events.values.flatMap { it.values.flatten() }
    this.ppos = ppos
    val parser = XcfaOcReasonParser(flatRfs union flatWss, flatEvents.toSet())
    var parseFailure = 0
    val propagatedClauses: List<Reason>
    logger.info(
      "Parse time (ms): " +
        measureTime {
            propagatedClauses =
              File(inputConflictClauseFile).readLines().mapNotNull { line ->
                try {
                  parser.parse(line)
                } catch (_: Exception) {
                  parseFailure++
                  null
                }
              }
          }
          .inWholeMilliseconds
    )

    val validConflicts: List<Reason>
    clauseValidationTime +=
      measureTime {
          validConflicts =
            propagatedClauses.filter { clause ->
              checkPath(clause).also { if (!it) System.err.println(clause) }
            }
        }
        .inWholeMilliseconds
    logger.info("Conflict clause parse failures: $parseFailure")
    logger.info("Parsed conflict clauses: ${propagatedClauses.size}")
    logger.info("Validated conflict clauses: ${validConflicts.size}")
    logger.info("Clause validation time (ms): $clauseValidationTime")

    if (permissive) {
      ocChecker.solver.add(validConflicts.map { Not(it.expr) })
    } else {
      nonOcSolver.add(validConflicts.map { Not(it.expr) })
    }
    val result: SolverStatus?
    logger.info(
      "Solver time (ms): " +
        measureTime {
            result =
              if (permissive) {
                ocChecker.check(events, pos, ppos, rfs, wss)
              } else {
                nonOcSolver.check()
              }
          }
          .inWholeMilliseconds
    )
    return result
  }

  private fun checkPath(combinedReason: Reason, from: E? = null, to: E? = null): Boolean {
    val reasons =
      combinedReason.reasons.filter { r ->
        when (r) {
          is RelationReason<*>,
          is WriteSerializationReason<*>,
          is FromReadReason<*> -> if (r.derivable()) true else return false

          is PoReason -> false
          else -> return false
        }
      }
    if (reasons.isEmpty()) return if (from != null) isPo(from, to!!) else false

    var possibleOrders =
      if (from == null) {
        val clkId = reasons.first().from.clkId
        if (reasons.all { it.from.clkId == clkId && it.to.clkId == clkId }) return false
        listOf(listOf(reasons.first()) to reasons.slice(1 until reasons.size))
      } else {
        reasons.filter { isPo(from, it.from) }.map { listOf(it) to reasons - it }
      }

    for (i in 1 until reasons.size) {
      val newPossibleOrders = mutableListOf<Pair<List<Reason>, List<Reason>>>()
      possibleOrders.forEach { po ->
        val previous = po.first.last()
        po.second
          .filter { isPo(previous.to, it.from) }
          .forEach { next -> newPossibleOrders.add(po.first + next to po.second - next) }
      }
      possibleOrders = newPossibleOrders
    }

    if (from != null) return possibleOrders.any { isPo(it.first.last().to, to!!) }
    return possibleOrders.any { isPo(it.first.last().to, it.first.first().from) } // check cylce
  }

  private fun isPo(from: E, to: E): Boolean {
    if(from.clkId == to.clkId) return true
    return ppos[from.clkId, to.clkId]
  }

  private fun isRf(rf: Relation<*>): Boolean =
    rf.from.const.varDecl == rf.to.const.varDecl &&
      rf.from.type == EventType.WRITE &&
      rf.to.type == EventType.READ

  private fun derivable(rf: Relation<*>, w: Event): Boolean =
    isRf(rf) && rf.from.const.varDecl == w.const.varDecl && w.type == EventType.WRITE

  private fun Reason.derivable(): Boolean =
    when (this) {
      is PoReason -> false
      is CombinedReason -> reasons.all { it.derivable() }
      is RelationReason<*> -> isRf(this.relation)
      is WriteSerializationReason<*> -> {
        this as WriteSerializationReason<E>
        if (!derivable(rf, w)) false else checkPath(wBeforeRf, w, rf.to)
      }

      is FromReadReason<*> -> {
        this as FromReadReason<E>
        if (!derivable(rf, w)) false else checkPath(wAfterRf, rf.from, w)
      }

      else -> error("Unsupported reason type.")
    }
}
