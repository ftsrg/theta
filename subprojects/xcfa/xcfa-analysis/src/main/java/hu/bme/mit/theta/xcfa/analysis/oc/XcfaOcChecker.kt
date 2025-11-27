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
) : SafetyChecker<EmptyProof, Cex, XcfaPrec<UnitPrec>> {

  init {
    check(property == ErrorDetection.ERROR_LOCATION) {
      "Unsupported property by OC checker: $property. Consider using a specification transformation."
    }
  }

  private val xcfa =
    xcfa.optimizeFurther(
      ProcedurePassManager(
        listOf(
          AssumeFalseRemovalPass(),
          MutexToVarPass(),
          AtomicReadsOneWritePass(),
          LoopUnrollPass(2), // force loop unroll for BMC
        )
      )
    )

  private val conflictFinder = autoConflictConfig.conflictFinder(autoConflictBound)

  private val ocChecker: OcChecker<E> =
    decisionProcedure.checker(smtSolver, memoryModel).let { ocChecker ->
      if (conflictInput == null) ocChecker
      else XcfaOcCorrectnessValidator(ocChecker, conflictInput, !nonPermissiveValidation, logger)
    }

  override fun check(prec: XcfaPrec<UnitPrec>?): SafetyResult<EmptyProof, Cex> =
    let {
        logger.mainStep("Creating event graph...")
        val eg = XcfaToEventGraph(xcfa).create()

        if (eg.violations.isEmpty()) {
          return@let SafetyResult.safe(EmptyProof.getInstance())
        }

        logger.mainStep("Adding constraints...")
        addToSolver(eg, ocChecker.solver)
        val (preservedPos, preservedWss) = memoryModel.filter(eg.events, eg.pos, eg.wss)

        // "Manually" add some conflicts
        logger.info(
          "Auto conflict time (ms): " +
            measureTime {
                val conflicts =
                  conflictFinder.findConflicts(eg.events, preservedPos, eg.rfs, logger)
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
        when {
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
              val trace = try {
                XcfaOcTraceExtractor(xcfa, ocChecker, eg).trace
              } catch (e: Exception) {
                logger.info("OC checker trace extraction failed: ${e.message}")
                EmptyCex.getInstance()
              }
              SafetyResult.unsafe(trace, EmptyProof.getInstance())
            } else {
              SafetyResult.unsafe<EmptyProof, Cex>(EmptyCex.getInstance(), EmptyProof.getInstance())
            }
          }

          else -> SafetyResult.unknown()
        }
      }
      .also {
        logger.mainStep("OC checker result: $it")
        if (it.isSafe && xcfa.unsafeUnrollUsed && !acceptUnreliableSafe) {
          logger.mainStep("Incomplete loop unroll used: safe result is unreliable.")
          logger.mainStep(SafetyResult.unknown<EmptyProof, Cex>().toString())
          throw NotSolvableException()
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
  }
}
