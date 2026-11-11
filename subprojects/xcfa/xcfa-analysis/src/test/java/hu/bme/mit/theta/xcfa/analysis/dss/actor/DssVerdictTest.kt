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
package hu.bme.mit.theta.xcfa.analysis.dss.actor

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.END_TO_END_TIMEOUT
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssGeneralizerCombination
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssGeneralizerKind
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.hasInternalCycle
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.reverseBlockGraph
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.reverseProgram
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.AcyclicMergeDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.CutLoopHandling
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.MergeBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.MinCutDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.SelfLoopAbsorbingDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.cut
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import java.util.stream.Stream
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

/** End-to-end verdicts of the sequential executor, with real CEGAR block analyses. */
class DssVerdictTest {

  enum class Decomposition(val decompose: (XcfaProcedure) -> BlockGraph) {
    LINEAR({ LinearBlockDecomposition().decompose(it) }),
    MERGE({ MergeBlockDecomposition(2).decompose(it) }),
    ABSORB_SELF_LOOPS({ SelfLoopAbsorbingDecomposition().decompose(it) }),
    ACYCLIC({ AcyclicMergeDecomposition().decompose(it) }),
    MIN_CUT({ MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW).cut(it).blockGraph }),
    MIN_CUT_ABSORB({
      MinCutDecomposition(loopHandling = CutLoopHandling.ABSORB_SELF_LOOPS).cut(it).blockGraph
    }),
    MIN_CUT_ACYCLIC({
      MinCutDecomposition(loopHandling = CutLoopHandling.FORBID).cut(it).blockGraph
    }),
  }

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }

    private val loopFree: Map<String, (Boolean) -> XCFA> =
      mapOf("branch" to ::branchXcfa, "three-way join" to ::threeWayJoinXcfa)

    private val loops: Map<String, (Boolean) -> XCFA> =
      mapOf(
        "xy loop" to ::xyLoopXcfa,
        "loop with a branching body" to ::branchingBodyLoopXcfa,
        "loop with a break" to ::loopWithBreakXcfa,
        "sequential loops" to ::sequentialLoopsXcfa,
        "guarded loop" to ::guardedLoopXcfa,
        "error inside a loop" to ::errorInLoopXcfa,
        "nondeterministic counter" to ::counterXcfa,
      )

    private val programs = loopFree + loops

    /**
     * DSS does not terminate on the safe error-inside-a-loop program when the loop stays a cycle of
     * the block graph (termination is not guaranteed).
     */
    private val cyclic =
      setOf(Decomposition.LINEAR, Decomposition.MERGE, Decomposition.ABSORB_SELF_LOOPS)

    /** Loop-free programs only need the decompositions that do not special-case loops. */
    @JvmStatic
    fun cases(): Stream<Arguments> {
      val loopFreeCases =
        loopFree.keys.flatMap { listOf(it to Decomposition.LINEAR, it to Decomposition.MERGE) }
      val loopCases = loops.keys.flatMap { p -> Decomposition.entries.map { p to it } }
      return (loopFreeCases + loopCases)
        .flatMap { (program, decomposition) ->
          listOf(true, false).map { safe -> Arguments.of(program, decomposition, safe) }
        }
        .filterNot {
          it.get()[0] == "error inside a loop" && it.get()[2] == true && it.get()[1] in cyclic
        }
        .stream()
    }

    /** Every loop program, with a cyclic, an acyclic and an absorbing block graph. */
    @JvmStatic
    fun generalizationCases(): Stream<Arguments> =
      loops.keys
        .flatMap { program ->
          listOf(Decomposition.LINEAR, Decomposition.ACYCLIC, Decomposition.MIN_CUT_ABSORB)
            .flatMap { d -> listOf(true, false).map { safe -> Arguments.of(program, d, safe) } }
        }
        .filterNot {
          it.get()[0] == "error inside a loop" && it.get()[2] == true && it.get()[1] in cyclic
        }
        .stream()

    /** The generalization cases, with both generalizers under each combination but FIRST. */
    @JvmStatic
    fun combinationCases(): Stream<Arguments> =
      generalizationCases()
        .toList()
        .flatMap { case ->
          listOf(DssGeneralizerCombination.UNION, DssGeneralizerCombination.CHAIN).map {
            Arguments.of(*case.get(), it)
          }
        }
        .stream()

    /** Every loop program, with the cyclic block graphs too, where plain DSS can diverge. */
    @JvmStatic
    fun conjectureCases(): Stream<Arguments> =
      loops.keys
        .flatMap { program ->
          (cyclic + Decomposition.ACYCLIC).flatMap { d ->
            listOf(true, false).map { safe -> Arguments.of(program, d, safe) }
          }
        }
        .stream()

    /** Every program on the decompositions that keep loops as cycles of blocks. */
    @JvmStatic
    fun wrongConjectureCases(): Stream<Arguments> =
      programs.keys
        .flatMap { program ->
          listOf(Decomposition.LINEAR, Decomposition.MERGE).flatMap { d ->
            listOf(true, false).map { safe -> Arguments.of(program, d, safe) }
          }
        }
        .stream()

    /** Every program, both new directions, the default and an acyclic decomposition. */
    @JvmStatic
    fun directionCases(): Stream<Arguments> =
      programs.keys
        .flatMap { program ->
          listOf(Decomposition.LINEAR, Decomposition.MERGE, Decomposition.ACYCLIC).flatMap { d ->
            Direction.entries.flatMap { direction ->
              listOf(true, false).map { safe -> Arguments.of(program, d, direction, safe) }
            }
          }
        }
        .filterNot {
          it.get()[0] in backwardDivergent &&
            it.get()[1] in cyclic &&
            it.get()[2] == Direction.BACKWARD &&
            it.get()[3] == true
        }
        .stream()

    /**
     * Backward DSS does not terminate on these safe programs when the reversed loop stays a cycle:
     * its postcondition, first computed from top, is not the least fixpoint and admits every
     * unrolling.
     */
    private val backwardDivergent =
      setOf("guarded loop", "error inside a loop", "nondeterministic counter")

    @JvmStatic
    fun cutCases(): Stream<Arguments> =
      programs.keys
        .flatMap { p -> listOf(true, false).map { Arguments.of(p, it) } }
        // Cutting a loop block leaves a cyclic block graph, which that program diverges on
        .filterNot { it.get()[0] == "error inside a loop" && it.get()[1] == true }
        .stream()

    /**
     * Backward DSS may diverge once a cut makes a loop a cycle of blocks (see [backwardDivergent]).
     */
    @JvmStatic
    fun directionCutCases(): Stream<Arguments> =
      programs.keys
        .flatMap { p ->
          Direction.entries.flatMap { d -> listOf(true, false).map { Arguments.of(p, d, it) } }
        }
        .filterNot {
          it.get()[0] in backwardDivergent &&
            it.get()[1] == Direction.BACKWARD &&
            it.get()[2] == true
        }
        .stream()

    private fun branchXcfa(safe: Boolean): XCFA =
      xcfa("branch") {
        val main =
          procedure("main") {
            "x" type Int()
            (init to "branch") { "x" assign if (safe) "5" else "20" }
            ("branch" to "checkA") { assume("(< x 10)") }
            ("branch" to "checkB") { assume("(>= x 10)") }
            ("checkA" to final) { nop() }
            ("checkB" to err) { nop() }
          }
        main.start()
      }

    private fun threeWayJoinXcfa(safe: Boolean): XCFA =
      xcfa("three-way-join") {
        val main =
          procedure("main") {
            "x" type Int()
            "y" type Int()
            (init to "branch") { havoc("y") }
            ("branch" to "arm1") { assume("(< y 0)") }
            ("branch" to "arm2") { assume("(= y 5)") }
            ("branch" to "arm3") { assume("(> y 100)") }
            ("arm1" to "join") { "x" assign "1" }
            ("arm2" to "join") { "x" assign "2" }
            ("arm3" to "join") { "x" assign if (safe) "3" else "15" }
            ("join" to "checkSafe") { assume("(< x 10)") }
            ("join" to "checkErr") { assume("(>= x 10)") }
            ("checkSafe" to final) { nop() }
            ("checkErr" to err) { nop() }
          }
        main.start()
      }

    /** Btor2C's counters: the loop's own postcondition must keep growing for several rounds. */
    private fun counterXcfa(safe: Boolean): XCFA =
      xcfa("counter") {
        val main =
          procedure("main") {
            "x" type Int()
            (init to "loophead") { "x" assign "1" }
            ("loophead" to err) { assume(if (safe) "(= x 5)" else "(= x 4)") }
            ("loophead" to "step") { assume(if (safe) "(/= x 5)" else "(/= x 4)") }
            ("step" to "loophead") { nop() }
            ("step" to "inc") { assume("(< x 4)") }
            ("step" to "wrap") { assume("(>= x 4)") }
            ("inc" to "loophead") { "x" assign "(+ x 1)" }
            ("wrap" to "loophead") { "x" assign "1" }
          }
        main.start()
      }

    private fun xyLoopXcfa(safe: Boolean): XCFA =
      xcfa("xy-loop") {
        val main =
          procedure("main") {
            "x" type Int()
            "y" type Int()
            (init to "loophead") {
              "x" assign "0"
              "y" assign "0"
            }
            ("loophead" to "body") { assume("(< x 2)") }
            ("loophead" to "afterloop") { assume("(>= x 2)") }
            ("body" to "loophead") {
              "x" assign "(+ x 1)"
              "y" assign if (safe) "(+ y 1)" else "y"
            }
            ("afterloop" to final) { assume("(= x y)") }
            ("afterloop" to err) { assume("(/= x y)") }
          }
        main.start()
      }

    private fun branchingBodyLoopXcfa(safe: Boolean): XCFA =
      xcfa("branching-body-loop") {
        val main =
          procedure("main") {
            "x" type Int()
            "y" type Int()
            "flag" type Int()
            (init to "loophead") {
              "x" assign "0"
              "y" assign "0"
            }
            ("loophead" to "body") {
              assume("(< x 2)")
              havoc("flag")
            }
            ("loophead" to "afterloop") { assume("(>= x 2)") }
            ("body" to "bodyA") { assume("(= flag 0)") }
            ("body" to "bodyB") { assume("(/= flag 0)") }
            ("bodyA" to "bodyJoin") {
              "x" assign "(+ x 1)"
              "y" assign "(+ y 1)"
            }
            ("bodyB" to "bodyJoin") {
              "x" assign "(+ x 1)"
              "y" assign if (safe) "(+ y 1)" else "y"
            }
            ("bodyJoin" to "loophead") { nop() }
            ("afterloop" to final) { assume("(= x y)") }
            ("afterloop" to err) { assume("(/= x y)") }
          }
        main.start()
      }

    private fun loopWithBreakXcfa(safe: Boolean): XCFA =
      xcfa("loop-with-break") {
        val main =
          procedure("main") {
            "x" type Int()
            (init to "loophead") { "x" assign "0" }
            ("loophead" to "body") { assume("(< x 4)") }
            ("loophead" to "afterloop") { assume("(>= x 4)") }
            ("body" to "checkBreak") { "x" assign "(+ x 1)" }
            ("checkBreak" to "afterloop") { assume("(>= x 2)") }
            ("checkBreak" to "loophead") { assume("(< x 2)") }
            val bound = if (safe) "100" else "2"
            ("afterloop" to final) { assume("(< x $bound)") }
            ("afterloop" to err) { assume("(>= x $bound)") }
          }
        main.start()
      }

    private fun sequentialLoopsXcfa(safe: Boolean): XCFA =
      xcfa("sequential-loops") {
        val main =
          procedure("main") {
            "x" type Int()
            "y" type Int()
            (init to "loop1head") { "x" assign "0" }
            ("loop1head" to "loop1body") { assume("(< x 2)") }
            ("loop1head" to "mid") { assume("(>= x 2)") }
            ("loop1body" to "loop1head") { "x" assign "(+ x 1)" }
            ("mid" to "loop2head") { "y" assign "0" }
            ("loop2head" to "loop2body") { assume("(< y 2)") }
            ("loop2head" to "afterloop2") { assume("(>= y 2)") }
            ("loop2body" to "loop2head") { "y" assign "(+ y 1)" }
            val error = if (safe) "(< x 2)" else "(>= x 2)"
            ("afterloop2" to final) { assume("(not $error)") }
            ("afterloop2" to err) { assume(error) }
          }
        main.start()
      }

    private fun guardedLoopXcfa(safe: Boolean): XCFA =
      xcfa("guarded-loop") {
        val main =
          procedure("main") {
            "x" type Int()
            "n" type Int()
            (init to "branch") {
              "x" assign "0"
              havoc("n")
            }
            ("branch" to final) { assume("(< n 0)") }
            ("branch" to "loophead") { assume("(>= n 0)") }
            ("loophead" to "body") { assume("(< x n)") }
            ("body" to "loophead") { "x" assign "(+ x 1)" }
            ("loophead" to "afterloop") { assume("(>= x n)") }
            val error = if (safe) "(/= x n)" else "(= x 2)"
            ("afterloop" to final) { assume("(not $error)") }
            ("afterloop" to err) { assume(error) }
          }
        main.start()
      }

    private fun errorInLoopXcfa(safe: Boolean): XCFA =
      xcfa("error-in-loop") {
        val main =
          procedure("main") {
            "x" type Int()
            "n" type Int()
            (init to "branch") {
              "x" assign "0"
              havoc("n")
            }
            ("branch" to final) { assume("(< n 0)") }
            ("branch" to "loophead") { assume("(>= n 0)") }
            ("loophead" to "check") {
              assume("(< x n)")
              "x" assign "(+ x 1)"
            }
            val bad = if (safe) "(- 0 1)" else "2"
            ("check" to err) { assume("(= x $bad)") }
            ("check" to "loophead") { assume("(/= x $bad)") }
            ("loophead" to final) { assume("(>= x n)") }
          }
        main.start()
      }
  }

  private fun cegarChecker(xcfa: XCFA) =
    getCegarChecker(
      xcfa,
      emptySet(),
      ParseContext(),
      getDefaultPredCegarConfig(),
      NullLogger.getInstance(),
    )

  private fun checkDecomposed(
    wholeProgram: XCFA,
    blockGraph: BlockGraph,
    useGlobalPredicatePool: Boolean = true,
    generalizationGas: Int = 0,
    generalizers: List<DssGeneralizerKind> = listOf(DssGeneralizerKind.GSPACER),
    combination: DssGeneralizerCombination = DssGeneralizerCombination.FIRST,
  ): DssResult {
    blockGraph.checkConsistency()
    val procedure = wholeProgram.procedures.single()
    val roster = DssCheckerRoster(listOf { x -> cegarChecker(x) })
    return assertTimeoutPreemptively<DssResult>(END_TO_END_TIMEOUT) {
      runDssActorsSequentially(
        blockGraph,
        behaviorFor = { block ->
          PredicateBlockBehavior(
            wholeProgram,
            procedure,
            block,
            roster,
            useGlobalPredicatePool,
            generalizationGas = generalizationGas,
            generalizers = generalizers,
            generalizerCombination = combination,
          )
        },
      )
    }
  }

  @ParameterizedTest(name = "{0}, {1}, safe={2}")
  @MethodSource("generalizationCases")
  fun `semantic generalization keeps the verdict`(
    program: String,
    decomposition: Decomposition,
    safe: Boolean,
  ) {
    val xcfa = programs.getValue(program)(safe)
    val blockGraph = decomposition.decompose(xcfa.procedures.single())
    val semantic = listOf(DssGeneralizerKind.SEMANTIC)
    assertEquals(
      expected(safe),
      checkDecomposed(xcfa, blockGraph, generalizationGas = 2, generalizers = semantic),
    )
  }

  @ParameterizedTest(name = "{3}: {0}, {1}, safe={2}")
  @MethodSource("combinationCases")
  fun `combined generalizers keep the verdict`(
    program: String,
    decomposition: Decomposition,
    safe: Boolean,
    combination: DssGeneralizerCombination,
  ) {
    val xcfa = programs.getValue(program)(safe)
    val blockGraph = decomposition.decompose(xcfa.procedures.single())
    val both = listOf(DssGeneralizerKind.GSPACER, DssGeneralizerKind.SEMANTIC)
    assertEquals(
      expected(safe),
      checkDecomposed(
        xcfa,
        blockGraph,
        generalizationGas = 2,
        generalizers = both,
        combination = combination,
      ),
    )
  }

  @ParameterizedTest(name = "{0}, {1}, safe={2}")
  @MethodSource("generalizationCases")
  fun `generalized violation conditions keep the verdict`(
    program: String,
    decomposition: Decomposition,
    safe: Boolean,
  ) {
    val xcfa = programs.getValue(program)(safe)
    val blockGraph = decomposition.decompose(xcfa.procedures.single())
    assertEquals(expected(safe), checkDecomposed(xcfa, blockGraph, generalizationGas = 2))
  }

  private fun expected(safe: Boolean) = if (safe) DssResult.SAFE else DssResult.UNSAFE

  /** [checkDecomposed] with a conjecture coordinator, which first proposes [initial]. */
  private fun checkWithConjectures(
    wholeProgram: XCFA,
    blockGraph: BlockGraph,
    gas: Int = 2,
    initial: List<Pair<XcfaLocation, Expr<BoolType>>> = emptyList(),
    generalizers: List<DssGeneralizerKind> = listOf(DssGeneralizerKind.GSPACER),
  ): DssResult {
    blockGraph.checkConsistency()
    val procedure = wholeProgram.procedures.single()
    val roster = DssCheckerRoster(listOf { x -> cegarChecker(x) })
    return assertTimeoutPreemptively<DssResult>(END_TO_END_TIMEOUT) {
      runDssNetworksSequentially(
          listOf(
            DssNetwork(blockGraph) { block ->
              PredicateBlockBehavior(wholeProgram, procedure, block, roster)
            }
          ),
          coordinator = { connection ->
            DssConjectureActor(
              connection,
              blockGraph,
              SolverManager.resolveSolverFactory("Z3"),
              gas,
              initialConjectures = initial,
              generalizers = generalizers,
            )
          },
        )
        .result
    }
  }

  @ParameterizedTest(name = "{0}, {1}, safe={2}")
  @MethodSource("conjectureCases")
  fun `semantic conjectures keep the verdict`(
    program: String,
    decomposition: Decomposition,
    safe: Boolean,
  ) {
    val xcfa = programs.getValue(program)(safe)
    val blockGraph = decomposition.decompose(xcfa.procedures.single())
    val semantic = listOf(DssGeneralizerKind.SEMANTIC)
    assertEquals(expected(safe), checkWithConjectures(xcfa, blockGraph, generalizers = semantic))
  }

  @ParameterizedTest(name = "{0}, {1}, safe={2}")
  @MethodSource("conjectureCases")
  fun `conjectured invariants keep the verdict`(
    program: String,
    decomposition: Decomposition,
    safe: Boolean,
  ) {
    val xcfa = programs.getValue(program)(safe)
    val blockGraph = decomposition.decompose(xcfa.procedures.single())
    assertEquals(expected(safe), checkWithConjectures(xcfa, blockGraph))
  }

  /**
   * Claims every block boundary unreachable: each reached one must be retracted, which leaves gas
   * for the generalized conjectures that a cyclic block graph still needs.
   */
  @ParameterizedTest(name = "{0}, {1}, safe={2}")
  @MethodSource("wrongConjectureCases")
  fun `a conjecture broken by a real path is retracted`(
    program: String,
    decomposition: Decomposition,
    safe: Boolean,
  ) {
    val xcfa = programs.getValue(program)(safe)
    val blockGraph = decomposition.decompose(xcfa.procedures.single())
    val boundaries = blockGraph.blocks.map { it.initialLocation }.distinct()
    val initial = boundaries.map { it to True() }
    assertEquals(expected(safe), checkWithConjectures(xcfa, blockGraph, initial = initial))
  }

  @ParameterizedTest(name = "{0}, {1}, safe={2}")
  @MethodSource("cases")
  fun `the decomposed verdict is the verdict of the program`(
    program: String,
    decomposition: Decomposition,
    safe: Boolean,
  ) {
    val xcfa = programs.getValue(program)(safe)
    val blockGraph = decomposition.decompose(xcfa.procedures.single())
    assertEquals(expected(safe), checkDecomposed(xcfa, blockGraph))
  }

  enum class Direction {
    BACKWARD,
    BIDIRECTIONAL,
    BIDIRECTIONAL_SHARING,
  }

  /** The verdict of [direction], run as `--dss-direction` runs it. */
  private fun checkDirection(
    wholeProgram: XCFA,
    decomposition: Decomposition,
    direction: Direction,
    cutEvery: Boolean = false,
  ): DssRun {
    val procedure = wholeProgram.procedures.single()
    val reversal = reverseProgram(wholeProgram)
    val roster = DssCheckerRoster(listOf { x -> cegarChecker(x) })
    val tracked = direction != Direction.BACKWARD
    fun behaviors(program: XCFA, programProcedure: XcfaProcedure) = { block: Block ->
      PredicateBlockBehavior(program, programProcedure, block, roster, trackSummaries = tracked)
    }
    return assertTimeoutPreemptively<DssRun>(END_TO_END_TIMEOUT) {
      if (direction == Direction.BACKWARD) {
        val graph =
          decomposition.decompose(reversal.procedure).cutEveryIf(cutEvery).also {
            it.checkConsistency()
          }
        runDssNetworksSequentially(
          listOf(DssNetwork(graph, behaviors(reversal.xcfa, reversal.procedure)))
        )
      } else {
        val forward = decomposition.decompose(procedure).cutEveryIf(cutEvery)
        val backward = reverseBlockGraph(forward, reversal).withIdPrefix("R.")
        backward.checkConsistency()
        runDssNetworksSequentially(
          listOf(
            DssNetwork(forward, behaviors(wholeProgram, procedure)),
            DssNetwork(backward, behaviors(reversal.xcfa, reversal.procedure)),
          ),
          coordinator = { connection ->
            DssMeetingActor(
              connection,
              procedure,
              DssMeetingSide(forward, procedure.locs.associateWith { it }),
              DssMeetingSide(backward, reversal.originalOf),
              SolverManager.resolveSolverFactory("Z3"),
              sharedVars = procedure.vars,
              shareInvariants = direction == Direction.BIDIRECTIONAL_SHARING,
            )
          },
        )
      }
    }
  }

  @ParameterizedTest(name = "{0}, {1}, {2}, safe={3}")
  @MethodSource("directionCases")
  fun `every direction gives the verdict of the program`(
    program: String,
    decomposition: Decomposition,
    direction: Direction,
    safe: Boolean,
  ) {
    val xcfa = programs.getValue(program)(safe)
    assertEquals(expected(safe), checkDirection(xcfa, decomposition, direction).result)
  }

  /** As `--dss-cut-on-timeout` cuts blocks, of the decomposition `EMERGENT` runs DSS with. */
  @ParameterizedTest(name = "{0}, safe={1}")
  @MethodSource("cutCases")
  fun `cutting every block keeps the verdict`(program: String, safe: Boolean) {
    val xcfa = programs.getValue(program)(safe)
    val decomposed = Decomposition.MIN_CUT_ABSORB.decompose(xcfa.procedures.single())
    val cut = decomposed.cutEveryIf(true)
    assertTrue(cut.blocks.size > decomposed.blocks.size) { "nothing to cut in $decomposed" }
    assertEquals(expected(safe), checkDecomposed(xcfa, cut))
  }

  /** As `--dss-cut-on-timeout` cuts in the new directions: BIDIRECTIONAL cuts the forward graph. */
  @ParameterizedTest(name = "{0}, {1}, safe={2}")
  @MethodSource("directionCutCases")
  fun `cutting every block keeps the verdict in both new directions`(
    program: String,
    direction: Direction,
    safe: Boolean,
  ) {
    val xcfa = programs.getValue(program)(safe)
    val run = checkDirection(xcfa, Decomposition.MIN_CUT_ABSORB, direction, cutEvery = true)
    assertEquals(expected(safe), run.result)
  }

  private fun BlockGraph.cutEveryIf(cut: Boolean): BlockGraph =
    if (!cut) this
    else
      blocks
        .map { it.id }
        .sorted()
        .fold(this) { g, id -> g.cut(id, MergeBlockDecomposition()) ?: g }

  @Test
  fun `without the global predicate pool, violation conditions refute the spurious error`() {
    val xcfa = branchXcfa(safe = true)
    val blockGraph = LinearBlockDecomposition().decompose(xcfa.procedures.single())
    assertEquals(DssResult.SAFE, checkDecomposed(xcfa, blockGraph, useGlobalPredicatePool = false))
  }

  @Test
  fun `a non-root block containing a loop sends per-path violation conditions`() {
    for (safe in listOf(true, false)) {
      val xcfa = guardedLoopXcfa(safe)
      val blockGraph = SelfLoopAbsorbingDecomposition().decompose(xcfa.procedures.single())
      val loopBlock = blockGraph.blocks.single { it.locations.any { loc -> loc.name == "body" } }
      assertTrue(hasInternalCycle(loopBlock) && !loopBlock.isRoot) { "fixture shape: $blockGraph" }
      assertEquals(expected(safe), checkDecomposed(xcfa, blockGraph))
    }
  }
}
