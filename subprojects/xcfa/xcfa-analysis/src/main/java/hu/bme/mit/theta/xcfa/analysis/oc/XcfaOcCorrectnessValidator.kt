/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
  decisionProcedure: OcDecisionProcedureType,
  private val inputConflictClauseFile: String,
  private val threads: Set<Thread>,
  private val permissive: Boolean = true,
  private val logger: Logger,
) : OcChecker<E> {

  private var clauseValidationTime = 0L
  private lateinit var exactPo: XcfaExactPo
  private lateinit var ocChecker: OcChecker<E>
  private lateinit var nonOcSolver: Solver

  init {
    if (permissive) {
      ocChecker = decisionProcedure.checker()
    } else {
      nonOcSolver = SolverManager.resolveSolverFactory("Z3:4.13").createSolver()
    }
  }

  override val solver
    get() = if (permissive) ocChecker.solver else nonOcSolver

  override fun getRelations() = if (permissive) ocChecker.getRelations() else null

  override fun getPropagatedClauses(): List<Reason> =
    if (permissive) ocChecker.getPropagatedClauses() else listOf()

  override fun check(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    pos: List<Relation<E>>,
    rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ): SolverStatus? {
    val flatRfs = rfs.values.flatten()
    val flatEvents = events.values.flatMap { it.values.flatten() }
    val parser = XcfaOcReasonParser(flatRfs.toSet(), flatEvents.toSet())
    var parseFailure = 0
    val propagatedClauses: List<Reason>
    logger.writeln(
      Logger.Level.INFO,
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
          .inWholeMilliseconds,
    )

    clauseValidationTime += measureTime { exactPo = XcfaExactPo(threads) }.inWholeMilliseconds

    val validConflicts: List<Reason>
    clauseValidationTime +=
      measureTime { validConflicts = propagatedClauses.filter { clause -> checkPath(clause) } }
        .inWholeMilliseconds
    logger.writeln(Logger.Level.INFO, "Conflict clause parse failures: $parseFailure")
    logger.writeln(Logger.Level.INFO, "Parsed conflict clauses: ${propagatedClauses.size}")
    logger.writeln(Logger.Level.INFO, "Validated conflict clauses: ${validConflicts.size}")
    logger.writeln(Logger.Level.INFO, "Clause validation time (ms): $clauseValidationTime")

    if (permissive) {
      ocChecker.solver.add(validConflicts.map { Not(it.expr) })
    } else {
      nonOcSolver.add(validConflicts.map { Not(it.expr) })
    }
    val result: SolverStatus?
    logger.writeln(
      Logger.Level.INFO,
      "Solver time (ms): " +
        measureTime {
            result =
              if (permissive) {
                ocChecker.check(events, pos, rfs, wss)
              } else {
                nonOcSolver.check()
              }
          }
          .inWholeMilliseconds,
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

  private fun isPo(from: E, to: E): Boolean = exactPo.isPo(from, to)

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
    }

  private val Reason.from: E
    get() =
      when (this) {
        is RelationReason<*> -> (this as RelationReason<E>).relation.from
        is WriteSerializationReason<*> -> (this as WriteSerializationReason<E>).w
        is FromReadReason<*> -> (this as FromReadReason<E>).rf.to
        else -> error("Unsupported reason type.")
      }

  private val Reason.to: E
    get() =
      when (this) {
        is RelationReason<*> -> (this as RelationReason<E>).relation.to
        is WriteSerializationReason<*> -> (this as WriteSerializationReason<E>).rf.from
        is FromReadReason<*> -> (this as FromReadReason<E>).w
        else -> error("Unsupported reason type.")
      }
}
