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

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNodeComparators
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgCegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgRefiner
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.expl.ExplOrd
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceBwBinItpChecker
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.analysis.ptr.ItpRefToPtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.ptr.getPtrPartialOrd
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.oc.AutoConflictFinderConfig
import hu.bme.mit.theta.xcfa.analysis.oc.OcDecisionProcedureType
import hu.bme.mit.theta.xcfa.analysis.oc.XcfaOcChecker
import hu.bme.mit.theta.xcfa.analysis.por.XcfaSporLts
import hu.bme.mit.theta.xcfa.passes.DataRaceToReachabilityPass
import hu.bme.mit.theta.xcfa.model.JoinLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isDataRacePossible
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

class XcfaDataRaceTest {

  private val parseContext = ParseContext()

  companion object {

    @JvmStatic
    fun data(): Collection<Array<Any>> {
      return listOf(
        arrayOf("/04multithread.c", false, SafetyResult<*, *>::isSafe),
        arrayOf("/05datarace.c", true, SafetyResult<*, *>::isUnsafe),
        arrayOf("/06ptrdatarace.c", true, SafetyResult<*, *>::isSafe),
        arrayOf("/07mutex.c", true, SafetyResult<*, *>::isSafe),
      )
    }

    @JvmStatic
    fun atomicData(): Collection<Array<Any>> {
      return listOf(
        arrayOf("/09atomicfield_norace.c", SafetyResult<*, *>::isSafe),
        arrayOf("/10plainfield_race.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/11atomicarray_norace.c", SafetyResult<*, *>::isSafe),
      )
    }
  }

  /**
   * Threads created and joined through an array of handles -- `pthread_t t[N]; for (i)
   * pthread_create(&t[i], …)` -- must each become a distinct thread, which the pidVar identifies. The
   * loops are unrolled and the index folded ([PthreadArrayHandleUnrollPass]), then each `&t[i]` / `t[i]`
   * keys its own handle ([CLibraryFunctionsPass]); conflating them would spawn just one thread and hide
   * every race the array's threads have. Checked structurally, so it does not depend on any one engine
   * finding the race.
   */
  @org.junit.jupiter.api.Test
  fun pthreadArrayHandlesAreDistinctThreads() {
    val stream = javaClass.getResourceAsStream("/12pthread_array_race.c")
    val xcfa =
      getXcfaFromC(
          stream!!,
          ParseContext(),
          false,
          XcfaProperty(ErrorDetection.DATA_RACE),
          NullLogger.getInstance(),
        )
        .first
    val startPidVars =
      xcfa.procedures
        .flatMap { it.edges }
        .flatMap { it.label.getFlatLabels() }
        .filterIsInstance<StartLabel>()
        .map { it.pidVar }
    Assertions.assertEquals(2, startPidVars.size, "both array elements spawn a thread")
    Assertions.assertEquals(2, startPidVars.toSet().size, "with distinct handles")
    val joinPidVars =
      xcfa.procedures
        .flatMap { it.edges }
        .flatMap { it.label.getFlatLabels() }
        .filterIsInstance<JoinLabel>()
        .map { it.pidVar }
        .toSet()
    Assertions.assertEquals(startPidVars.toSet(), joinPidVars, "each thread is joined on its handle")
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testDataRacePreCheck(
    program: String,
    expectedDataRacePossible: Boolean,
    verdict: (SafetyResult<*, *>) -> Boolean,
  ) {
    println("Testing $program for trivial no data race...")
    val property = XcfaProperty(ErrorDetection.DATA_RACE)
    val stream = javaClass.getResourceAsStream(program)
    val xcfa =
      getXcfaFromC(stream!!, ParseContext(), false, property, NullLogger.getInstance()).first
    val dataRacePossible = isDataRacePossible(xcfa)
    Assertions.assertEquals(expectedDataRacePossible, dataRacePossible)
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testDataRaceCegarChecker(
    program: String,
    expectedDataRacePossible: Boolean,
    verdict: (SafetyResult<*, *>) -> Boolean,
  ) {
    println("Testing $program for data race...")
    Assertions.assertTrue(verdict(checkWithCegar(program)))
  }

  /**
   * `_Atomic` is a property of the accessed cell, not of the pointer expression that reaches it. A
   * struct field, array element, whole struct, nested field or pointee declared `_Atomic` is reached
   * through a `(base, offset)` dereference whose C type is gone by analysis time, so its atomicity is
   * resolved from the object's base id. These pin that the race check excludes such accesses -- and,
   * via the plain-field control, that it still reports races on non-atomic cells of the same object.
   */
  @ParameterizedTest
  @MethodSource("atomicData")
  fun testAtomicCellDataRace(program: String, verdict: (SafetyResult<*, *>) -> Boolean) {
    println("Testing $program for atomic-cell data race...")
    Assertions.assertTrue(verdict(checkWithCegar(program)), program)
  }

  private fun checkWithCegar(program: String): SafetyResult<*, *> {
    val property = XcfaProperty(ErrorDetection.DATA_RACE)
    val stream = javaClass.getResourceAsStream(program)
    // One parse context throughout: the atomic-cell facts recorded while building the XCFA are read
    // back by the error detector below, so it must be the same instance, not a fresh empty one.
    val parseContext = ParseContext()
    val xcfa = getXcfaFromC(stream!!, parseContext, false, property, NullLogger.getInstance()).first

    val analysis =
      ExplXcfaAnalysis(
        xcfa,
        Z3LegacySolverFactory.getInstance().createSolver(),
        1,
        getPartialOrder(ExplOrd.getInstance().getPtrPartialOrd()),
        false,
      )

    val lts = XcfaSporLts(xcfa)

    val errorDetector = getXcfaErrorDetector(property.verifiedProperty, parseContext)
    val abstractor =
      getXcfaAbstractor(
        analysis,
        PriorityWaitlist.create(
          ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.dfs())
        ),
        StopCriterions.firstCex<XcfaState<PtrState<ExplState>>, XcfaAction>(),
        ConsoleLogger(Logger.Level.DETAIL),
        lts,
        errorDetector,
      )
        as ArgAbstractor<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

    val precRefiner =
      XcfaPrecRefiner<XcfaState<PtrState<ExplState>>, ExplPrec, ItpRefutation>(
        ItpRefToPtrPrec(ItpRefToExplPrec())
      )

    val refiner =
      XcfaSingleExprTraceRefiner.create(
        ExprTraceBwBinItpChecker.create(
          BoolExprs.True(),
          BoolExprs.True(),
          Z3LegacySolverFactory.getInstance().createItpSolver(),
        ),
        precRefiner,
        PruneStrategy.FULL,
        NullLogger.getInstance(),
      ) as ArgRefiner<XcfaState<PtrState<ExplState>>, XcfaAction, XcfaPrec<PtrPrec<ExplPrec>>>

    val cegarChecker = ArgCegarChecker.create(abstractor, refiner)
    return cegarChecker.check(XcfaPrec(PtrPrec(ExplPrec.empty(), emptySet())))
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testDataRaceOcChecker(
    program: String,
    expectedDataRacePossible: Boolean,
    verdict: (SafetyResult<*, *>) -> Boolean,
  ) {
    println("Testing $program for data race...")
    val property = XcfaProperty(ErrorDetection.DATA_RACE)
    SolverManager.registerSolverManager(hu.bme.mit.theta.solver.z3.Z3SolverManager.create())
    DataRaceToReachabilityPass.enabled = true
    val stream = javaClass.getResourceAsStream(program)
    val parseContext = ParseContext()
    val xcfa = getXcfaFromC(stream!!, parseContext, false, property, NullLogger.getInstance()).first
    DataRaceToReachabilityPass.enabled = false

    val ocChecker =
      XcfaOcChecker(
        xcfa = xcfa,
        property = property,
        parseContext = parseContext,
        decisionProcedure = OcDecisionProcedureType.BASIC,
        smtSolver = "Z3:4.13",
        logger = NullLogger.getInstance(),
        conflictInput = null,
        outputConflictClauses = false,
        nonPermissiveValidation = false,
        autoConflictConfig = AutoConflictFinderConfig.NONE,
        autoConflictBound = -1,
      )

    val safetyResult = ocChecker.check(null)
    Assertions.assertTrue(verdict(safetyResult))
  }
}
