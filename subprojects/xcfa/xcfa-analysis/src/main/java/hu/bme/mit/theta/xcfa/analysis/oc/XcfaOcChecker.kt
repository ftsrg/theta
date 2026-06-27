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

import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.EmptyCex
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.oc.OcChecker
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.oc.XcfaOcMemoryConsistencyModel.SC
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.optimizeFurther
import hu.bme.mit.theta.xcfa.passes.*
import kotlin.time.measureTime

class XcfaOcChecker(
  xcfa: XCFA,
  property: ErrorDetection,
  decisionProcedure: OcDecisionProcedureType,
  smtSolver: String,
  private val logger: Logger,
  conflictInput: String?,
  private val outputConflictClauses: Boolean,
  nonPermissiveValidation: Boolean,
  autoConflictConfig: AutoConflictFinderConfig,
  autoConflictBound: Int,
  private val memoryModel: XcfaOcMemoryConsistencyModel = SC,
  private val acceptUnreliableSafe: Boolean = false,
  private val forceUnrollBoundStart: Int = 2,
  private val forceUnrollBoundEnd: Int = 2,
  private val forceUnrollBoundStep: Int = 1,
  private val witnessOptimizations: Boolean = false,
) : SafetyChecker<EmptyProof, Cex, XcfaPrec<UnitPrec>> {

  init {
    check(property == ErrorDetection.ERROR_LOCATION) {
      "Unsupported property by OC checker: $property. Consider using a specification transformation."
    }
  }

  val xcfa =
    xcfa.optimizeFurther(
      ProcedurePassManager(
        listOf(AssumeFalseRemovalPass(), MutexToVarPass(), AtomicReadsOneWritePass())
      )
    )

  private val conflictFinder = autoConflictConfig.conflictFinder(autoConflictBound)

  private val ocChecker: OcChecker<E> =
    decisionProcedure.checker(smtSolver, memoryModel).let { ocChecker ->
      if (conflictInput == null) ocChecker
      else XcfaOcCorrectnessValidator(ocChecker, conflictInput, !nonPermissiveValidation, logger)
    }

  override fun check(prec: XcfaPrec<UnitPrec>?): SafetyResult<EmptyProof, Cex> {
    // A negative upper bound means "unbounded": keep deepening the force-unroll bound (BMC-style)
    // until a reliable result is found or resources run out.
    val unbounded = forceUnrollBoundEnd < 0
    require(forceUnrollBoundStep > 0) { "Force unroll bound step must be positive." }
    require(unbounded || forceUnrollBoundStart <= forceUnrollBoundEnd) {
      "Empty unroll bound range: $forceUnrollBoundStart..$forceUnrollBoundEnd"
    }
    var i = forceUnrollBoundStart
    while (unbounded || i <= forceUnrollBoundEnd) {
      logger.mainStep("\nChecking with force loop unroll bound: $i")
      val (result, unsafeUnrollUsed) = check(i)
      logger.mainStep("OC checker result: $result")
      if (!result.isSafe || !unsafeUnrollUsed || acceptUnreliableSafe) {
        return result
      }
      logger.mainStep("Incomplete loop unroll bound ($i) used: safe result is unreliable.")
      i += forceUnrollBoundStep
    }

    logger.mainStep(SafetyResult.unknown<EmptyProof, Cex>().toString())
    throw NotSolvableException()
  }

  /**
   * Checks the XCFA after force unrolling loops the given number of times.
   *
   * Returns a safety result and a boolean indicating whether force unroll was indeed used. If true,
   * a safe result is unreliable.
   */
  private fun check(forceUnrollBound: Int): Pair<SafetyResult<EmptyProof, Cex>, Boolean> {
    // force loop unroll for BMC
    val xcfa = xcfa.optimizeFurther(ProcedurePassManager(listOf(LoopUnrollPass(forceUnrollBound))))

    logger.mainStep("Creating event graph...")
    val eg = XcfaToEventGraph(xcfa).create()

    return check(eg) to xcfa.unsafeUnrollUsed
  }

  private fun check(eg: XcfaToEventGraph.EventGraph): SafetyResult<EmptyProof, Cex> {
    if (eg.violations.isEmpty()) {
      return SafetyResult.safe(EmptyProof.getInstance())
    }

    logger.info("Adding constraints...")
    addToSolver(eg, ocChecker.solver)
    val (preservedPos, preservedWss) = memoryModel.filter(eg.events, eg.pos, eg.wss)

    // "Manually" add some conflicts
    logger.info(
      "Auto conflict time (ms): " +
        measureTime {
            val conflicts = conflictFinder.findConflicts(eg.events, preservedPos, eg.rfs, logger)
            ocChecker.solver.add(conflicts.map { Not(it.expr) })
            logger.info("Auto conflicts: ${conflicts.size}")
          }
          .inWholeMilliseconds
    )

    logger.mainStep("Start checking...")
    val status: SolverStatus?
    val checkerTime = measureTime {
      status = ocChecker.check(eg.events, eg.pos, preservedPos, eg.rfs, preservedWss)
    }
    if (ocChecker !is XcfaOcCorrectnessValidator)
      logger.info("Solver time (ms): ${checkerTime.inWholeMilliseconds}")
    logger.info("Propagated clauses: ${ocChecker.getPropagatedClauses().size}")

    ocChecker.solver.statistics.let {
      logger.info("Solver statistics:")
      it.forEach { (k, v) -> logger.info("$k: $v") }
    }

    return when {
      status?.isUnsat == true -> {
        if (outputConflictClauses)
          System.err.println(
            "Conflict clause output time (ms): ${
              measureTime {
                ocChecker.getPropagatedClauses().forEach { System.err.println("CC: $it") }
              }.inWholeMilliseconds
            }"
          )
        SafetyResult.safe(EmptyProof.getInstance())
      }

      status?.isSat == true -> {
        if (ocChecker is XcfaOcCorrectnessValidator)
          return SafetyResult.unsafe(EmptyCex.getInstance(), EmptyProof.getInstance())
        if (memoryModel == SC) {
          val trace =
            try {
              XcfaOcTraceExtractor(xcfa, ocChecker, eg).trace
            } catch (e: Exception) {
              logger.info("OC checker trace extraction failed: ${e.message}")
              EmptyCex.getInstance()
            }
          SafetyResult.unsafe(trace, EmptyProof.getInstance())
        } else {
          SafetyResult.unsafe(EmptyCex.getInstance(), EmptyProof.getInstance())
        }
      }

      else -> SafetyResult.unknown()
    }
  }

  private fun addToSolver(eg: XcfaToEventGraph.EventGraph, solver: Solver) {
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

    if (witnessOptimizations) {
      eg.wss.forEach { (v, rels) ->
        if (v.name == SEGMENT_COUNTER) {
          rels.forEach { rel ->
            val active = And(rel.from.guardExpr, rel.to.guardExpr)
            solver.add(Imply(And(rel.declRef, active), Leq(rel.from.const.ref, rel.to.const.ref)))
            solver.add(Imply(And(active, Lt(rel.from.const.ref, rel.to.const.ref)), rel.declRef))
          }
        }
      }
    }
  }

  companion object {
    /** The global segment counter introduced by the witness instrumentation (ApplyWitnessPass). */
    private const val SEGMENT_COUNTER = "__THETA__segment__counter__"
  }
}
