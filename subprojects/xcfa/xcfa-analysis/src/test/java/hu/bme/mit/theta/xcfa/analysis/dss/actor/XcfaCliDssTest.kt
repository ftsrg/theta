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

import hu.bme.mit.theta.xcfa.cli.XcfaCli
import hu.bme.mit.theta.xcfa.cli.params.Backend
import hu.bme.mit.theta.xcfa.cli.params.DssDecomposition
import hu.bme.mit.theta.xcfa.passes.loops.SpinLoopEffectPass
import hu.bme.mit.theta.xcfa.passes.memory.FetchExecuteWriteback
import hu.bme.mit.theta.xcfa.passes.memory.PtrSizeToMemoryPass
import hu.bme.mit.theta.xcfa.passes.property.DataRaceToReachabilityPass
import hu.bme.mit.theta.xcfa.passes.structure.LbePass
import hu.bme.mit.theta.xcfa.passes.structure.StaticCoiPass
import java.io.BufferedOutputStream
import java.io.FileOutputStream
import java.io.PrintStream
import java.util.stream.Stream
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.CsvSource
import org.junit.jupiter.params.provider.EnumSource
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource

private const val CUT = "--dss-cut-on-timeout"

class XcfaCliDssTest {

  companion object {

    @JvmStatic
    fun decompositions(): Stream<Arguments> =
      DssDecomposition.entries
        .flatMap { d -> listOf("loop", "loop_unsafe").map { Arguments.of(d.name, it) } }
        .stream()

    @JvmStatic
    fun directedDecompositions(): Stream<Arguments> =
      listOf("BACKWARD", "BIDIRECTIONAL")
        .flatMap { direction ->
          decompositions().toList().map { Arguments.of(direction, *it.get()) }
        }
        // Backward DSS does not terminate on the safe loop while the reversed loop stays a cycle
        .filterNot {
          it.get()[0] == "BACKWARD" &&
            it.get()[1] in setOf("LINEAR", "MERGE") &&
            it.get()[2] == "loop"
        }
        .stream()

    @JvmStatic
    fun options(): Stream<Arguments> =
      listOf(
          listOf("--output", "ALL"),
          listOf("--dss-reset-precision"),
          listOf("--dss-reuse-block-precision"),
          listOf("--dss-generalize-violations", "--dss-generalization-gas", "1"),
          listOf("--dss-generalizers", "SEMANTIC"),
          listOf(
            "--dss-generalizers",
            "SEMANTIC",
            "--dss-decomposition",
            "MIN_CUT_ABSORB_SELF_LOOPS",
          ),
          listOf("--dss-generalizers", "SEMANTIC", "--dss-semantic-unrollings", "0"),
          listOf(
            "--dss-generalizers",
            "GSPACER,SEMANTIC",
            "--dss-generalizer-combination",
            "UNION",
          ),
          listOf(
            "--dss-generalizers",
            "GSPACER,SEMANTIC",
            "--dss-generalizer-combination",
            "CHAIN",
          ),
          listOf("--dss-conjecture-invariants", "--dss-conjecture-generalizers", "SEMANTIC"),
          listOf(
            "--dss-conjecture-invariants",
            "--dss-conjecture-generalizers",
            "SEMANTIC,GSPACER",
            "--dss-generalizer-combination",
            "UNION",
          ),
          listOf("--dss-conjecture-invariants"),
          listOf("--dss-conjecture-invariants", "--dss-conjecture-gas", "1"),
          listOf("--dss-conjecture-invariants", "--dss-decomposition", "LINEAR"),
          listOf("--dss-conjecture-invariants", "--dss-executor", "CONCURRENT"),
          listOf("--dss-conjecture-invariants", "--dss-direction", "BACKWARD"),
          listOf("--dss-global-predicate-pool", "true"),
          listOf("--dss-cegar-domain", "EXPL"),
          listOf("--dss-cegar-domain", "EXPL", "--dss-reuse-block-precision"),
          listOf("--dss-checker-backends", "CEGAR,KIND", "--dss-checker-selection", "PRIORITY"),
          listOf("--dss-checker-backends", "CEGAR,KIND", "--dss-checker-selection", "FASTEST"),
          listOf("--dss-checker-backends", "CEGAR,BMC", "--dss-checker-selection", "ROUND_ROBIN"),
          listOf("--dss-checker-backends", "CEGAR,KIND", "--dss-checker-selection", "FINISHER"),
          listOf(
            "--dss-checker-backends",
            "CEGAR,KIND",
            "--dss-checker-selection",
            "FINISHER",
            "--dss-direction",
            "BACKWARD",
          ),
          // BIDIRECTIONAL accepts a bounded checker only as the finisher
          listOf(
            "--dss-checker-backends",
            "CEGAR,CEGAR",
            "--dss-checker-selection",
            "FINISHER",
            "--dss-direction",
            "BIDIRECTIONAL",
          ),
          listOf(
            "--dss-checker-backends",
            "CEGAR,KIND",
            "--dss-checker-selection",
            "FINISHER",
            "--dss-direction",
            "BIDIRECTIONAL",
          ),
          listOf(
            "--dss-checker-backends",
            "CEGAR,IMC",
            "--dss-checker-selection",
            "FINISHER",
            "--dss-direction",
            "BIDIRECTIONAL",
          ),
          listOf("--dss-checker-backends", "KIND"),
          listOf("--dss-checker-backends", "KIND", "--dss-interpolate-bounded-proofs", "false"),
          listOf("--dss-checker-backends", "BMC"),
          listOf("--dss-direction", "BACKWARD"),
          listOf("--dss-direction", "BACKWARD", "--dss-executor", "PROCESS"),
          listOf("--dss-direction", "BIDIRECTIONAL"),
          listOf("--dss-direction", "BIDIRECTIONAL", "--dss-share-invariants", "false"),
          listOf("--dss-direction", "BIDIRECTIONAL", "--dss-executor", "CONCURRENT"),
          listOf("--dss-direction", "BIDIRECTIONAL", "--dss-executor", "PROCESS"),
          listOf("--dss-checker-backends", "KIND,CEGAR", "--dss-checker-budget", "60000"),
          listOf("--dss-expl-checker", "--dss-checker-budget", "60000"),
          listOf("--dss-checker-backends", "KIND,CEGAR", "--dss-checker-budget", "1", CUT),
          listOf("--dss-checker-backends", "CEGAR,KIND", "--dss-fallback-solver", "Z3:new"),
          listOf("--dss-solver", "Z3"),
          listOf("--dss-quantified-predicates", "DROP"),
          listOf("--dss-quantified-predicates", "ELIMINATE"),
          listOf("--dss-quantified-predicates", "FALLBACK", "--dss-fallback-solver", "Z3:new"),
          listOf("--dss-block-local-pool"),
        )
        .flatMap { o -> listOf("safe", "unsafe").map { Arguments.of(o, it) } }
        .stream()
  }

  /**
   * With a 1 ms budget, every checker runs out of it, so the single block is cut until no piece has
   * a cut. Loop-free programs only: DSS need not terminate once a loop is cut into a cycle of
   * blocks.
   */
  private val cutting =
    arrayOf("--dss-decomposition", "NONE", "--dss-expl-checker", "--dss-checker-budget", "1", CUT)

  private fun expected(program: String) =
    if (program.endsWith("unsafe")) "SafetyResult Unsafe" else "SafetyResult Safe"

  @ParameterizedTest(name = "{0} on {1}")
  @MethodSource("decompositions")
  fun `every decomposition gives the right verdict`(decomposition: String, program: String) {
    assertTrue(
      dssVerdict(program, "--dss-decomposition", decomposition).contains(expected(program))
    )
  }

  @ParameterizedTest(name = "{0}, {1} on {2}")
  @MethodSource("directedDecompositions")
  fun `every decomposition gives the right verdict in both new directions`(
    direction: String,
    decomposition: String,
    program: String,
  ) {
    val verdict =
      dssVerdict(program, "--dss-direction", direction, "--dss-decomposition", decomposition)
    assertTrue(verdict.contains(expected(program))) { verdict }
  }

  @ParameterizedTest(name = "{0} on {1}")
  @MethodSource("options")
  fun `every option keeps the verdict`(options: List<String>, program: String) {
    assertTrue(dssVerdict(program, *options.toTypedArray()).contains(expected(program)))
  }

  @ParameterizedTest
  @EnumSource(Backend::class, names = ["CEGAR", "BMC", "KIND", "IMC", "KINDIMC", "BOUNDED"])
  fun `every checker backend finds the violation`(backend: Backend) {
    assertTrue(dssVerdict("unsafe", "--dss-checker-backends", backend.name).contains("Unsafe"))
  }

  @Test
  fun `a bidirectional run with a bounded block checker is rejected`() {
    val (output, thrown) =
      runDss("safe", "--dss-direction", "BIDIRECTIONAL", "--dss-checker-backends", "CEGAR,KIND")
    assertTrue(thrown != null && "cannot be certified" in output) { output }
  }

  @Test
  fun `a bidirectional run with a bounded checker other than the finisher is rejected`() {
    val (output, thrown) =
      runDss(
        "safe",
        "--dss-direction",
        "BIDIRECTIONAL",
        "--dss-checker-selection",
        "FINISHER",
        "--dss-checker-backends",
        "KIND,CEGAR",
      )
    assertTrue(thrown != null && "cannot be certified" in output) { output }
  }

  @ParameterizedTest
  @ValueSource(strings = ["--dss-direction=BIDIRECTIONAL", "--dss-executor=PROCESS"])
  fun `conjectures outside an in-process single network are rejected`(option: String) {
    val (name, value) = option.split("=")
    val (output, thrown) = runDss("safe", "--dss-conjecture-invariants", name, value)
    assertTrue(thrown != null && "--dss-conjecture-invariants needs" in output) { output }
  }

  @Test
  fun `a backend outside the DSS-compatible subset is rejected`() {
    val (output, thrown) = runDss("safe", "--dss-checker-backends", "OC")
    assertTrue(thrown != null && "OC" in output) { output }
  }

  @Test
  fun `a finisher without another backend is rejected`() {
    val (output, thrown) =
      runDss("safe", "--dss-checker-selection", "FINISHER", "--dss-checker-backends", "KIND")
    assertTrue(thrown != null && "at least two" in output) { output }
  }

  @Test
  fun `a checker budget without priority selection is rejected`() {
    val (output, thrown) =
      runDss("safe", "--dss-checker-budget", "1000", "--dss-checker-selection", "FASTEST")
    assertTrue(thrown != null && "--dss-checker-selection PRIORITY" in output) { output }
  }

  /**
   * `--dss-expl-checker` would come after the finisher, which must be the roster's last checker.
   */
  @Test
  fun `a finisher with the EXPL checker is rejected`() {
    val (output, thrown) =
      runDss(
        "safe",
        "--dss-checker-selection",
        "FINISHER",
        "--dss-checker-backends",
        "CEGAR,KIND",
        "--dss-expl-checker",
      )
    assertTrue(thrown != null && "--dss-expl-checker" in output) { output }
  }

  @Test
  fun `a query fallback without a fallback solver is rejected`() {
    val (output, thrown) = runDss("safe", "--dss-quantified-predicates", "FALLBACK")
    assertTrue(thrown != null && "--dss-quantified-predicates FALLBACK" in output) { output }
  }

  @Test
  fun `a negative semantic unrolling bound is rejected`() {
    val (output, thrown) = runDss("safe", "--dss-semantic-unrollings", "-1")
    assertTrue(thrown != null && "--dss-semantic-unrollings" in output) { output }
  }

  /** Later tests in this JVM build their XCFAs with the global pass switches the CLI sets. */
  @Test
  fun `a CLI run leaves the global pass switches as it found them`() {
    val before = LbePass.defaultLevel
    LbePass.defaultLevel = LbePass.LbeLevel.NO_LBE
    try {
      runDss("safe")
      assertEquals(LbePass.LbeLevel.NO_LBE, LbePass.defaultLevel)
    } finally {
      LbePass.defaultLevel = before
    }
  }

  @Test
  fun `cutting on timeout without a checker budget is rejected`() {
    val (output, thrown) = runDss("safe", CUT)
    assertTrue(thrown != null && "--dss-cut-on-timeout" in output) { output }
  }

  /**
   * Not with `PROCESS`: every restart starts new worker processes, which takes minutes.
   * `BIDIRECTIONAL` may finish from blocks that need no solver call before any budget runs out.
   */
  @ParameterizedTest
  @ValueSource(strings = ["FORWARD", "BACKWARD", "BIDIRECTIONAL"])
  fun `a block that every checker runs out of is cut, and the run starts over`(direction: String) {
    // BIDIRECTIONAL cannot cut in place, so the default also starts over there
    val restart =
      if (direction == "BIDIRECTIONAL") emptyArray() else arrayOf("--dss-cut-restart", "ALL")
    val cut =
      listOf("branches", "branches_unsafe").map { program ->
        val (output, thrown) =
          runDss(program, *cutting, *restart, "--dss-direction", direction, "--loglevel", "INFO")
        if (thrown != null) throw AssertionError(output, thrown)
        val verdict = output.lines().last { it.contains("SafetyResult") }
        assertTrue(verdict.contains(expected(program))) { output }
        "starting over with it cut" in output
      }
    assertTrue(if (direction == "BIDIRECTIONAL") cut.any { it } else cut.all { it }) { "$cut" }
  }

  /**
   * Loop-free programs only, as for [cutting]; [decomposition] decides how many blocks there are.
   */
  @ParameterizedTest(name = "{0}, {1}")
  @CsvSource("FORWARD,NONE", "FORWARD,MERGE", "BACKWARD,NONE", "BACKWARD,MERGE")
  fun `a cut block is replaced in place while the other blocks keep running`(
    direction: String,
    decomposition: String,
  ) {
    val cut =
      listOf("branches", "branches_unsafe").map { program ->
        val (output, thrown) =
          runDss(
            program,
            "--dss-expl-checker",
            "--dss-checker-budget",
            "1",
            CUT,
            "--dss-decomposition",
            decomposition,
            "--dss-direction",
            direction,
            "--loglevel",
            "INFO",
          )
        if (thrown != null) throw AssertionError(output, thrown)
        val verdict = output.lines().last { it.contains("SafetyResult") }
        assertTrue(verdict.contains(expected(program))) { output }
        assertTrue("starting over" !in output) { output }
        "replacing it by its pieces" in output
      }
    assertTrue(cut.any { it }) { "no block was cut in place: $cut" }
  }

  /** The cut uses the decomposition of the run unless `--dss-cut-strategy` names another. */
  @ParameterizedTest
  @EnumSource(DssDecomposition::class)
  fun `every decomposition can cut a block, and keeps the verdict`(strategy: DssDecomposition) {
    for (program in listOf("branches", "branches_unsafe")) {
      val (output, thrown) = runDss(program, *cutting, "--dss-cut-strategy", strategy.name)
      if (thrown != null) throw AssertionError(output, thrown)
      assertTrue(output.lines().last { it.contains("SafetyResult") }.contains(expected(program))) {
        output
      }
    }
  }

  @Test
  fun `a block is cut with the decomposition of the run unless another strategy is named`() {
    fun cuts(vararg options: String): List<String> {
      val (output, thrown) =
        runDss(
          "branches",
          "--dss-expl-checker",
          "--dss-checker-budget",
          "1",
          CUT,
          *options,
          "--loglevel",
          "INFO",
        )
      if (thrown != null) throw AssertionError(output, thrown)
      return output.lines().filter { "replacing it by its pieces" in it }
    }

    val merged = cuts("--dss-decomposition", "MERGE")
    assertTrue(merged.isNotEmpty()) { "no block was cut" }
    assertEquals(merged, cuts("--dss-decomposition", "MERGE", "--dss-cut-strategy", "MERGE"))
    // NONE cuts nothing, so a run that does not decompose cuts as MIN_CUT_ABSORB_SELF_LOOPS
    val single = cuts("--dss-decomposition", "NONE")
    assertTrue(single.isNotEmpty()) { "no block was cut" }
    assertEquals(
      single,
      cuts("--dss-decomposition", "NONE", "--dss-cut-strategy", "MIN_CUT_ABSORB_SELF_LOOPS"),
    )
  }

  @Test
  fun `properties a pass reduces to error-location reachability are checked`() {
    assertTrue(
      dssVerdict("overflow_unsafe", property = "no-overflow").contains("SafetyResult Unsafe")
    )
    assertTrue(
      dssVerdict("assert_unsafe", property = "no-assertion-violation")
        .contains("SafetyResult Unsafe")
    )
  }

  @Test
  fun `termination is rejected`() {
    val (output, thrown) = runDss("safe", property = "termination")
    assertTrue(thrown != null && "not TERMINATION" in output) { output }
  }

  @ParameterizedTest
  @ValueSource(strings = ["safe", "unsafe"])
  fun `--loglevel INFO prints exactly one SafetyResult line, the DSS verdict`(program: String) {
    val (output, thrown) = runDss(program, "--loglevel", "INFO", debug = false)
    assertEquals(null, thrown)
    val resultLines = output.lines().filter { it.contains("SafetyResult") }
    assertEquals(1, resultLines.size) { "$resultLines" }
    assertTrue(resultLines.single().contains(expected(program))) { resultLines.single() }
  }

  @Test
  fun `a SAFE run writes location invariants that Theta validates`() {
    val witness = dssWitness("loop", "SEQUENTIAL")
    assertTrue(witness.contains("entry_type: 'invariant_set'")) { witness }
    assertTrue(witness.contains("location_invariant")) { witness }
    assertTrue(verdictWithWitness("loop", witness).contains("SafetyResult Safe"))
  }

  /** Interpolation turns k-induction proofs into invariants over the program variables. */
  @Test
  fun `a SAFE run of k-induction blocks writes location invariants that Theta validates`() {
    val witness = dssWitness("loop", "SEQUENTIAL", checkers = "KIND")
    assertTrue(witness.contains("location_invariant")) { witness }
    assertTrue(verdictWithWitness("loop", witness).contains("SafetyResult Safe"))
  }

  /** After inlining, every C function's statements see the variables of all the others. */
  @Test
  fun `invariants name only the variables in scope at their statement`() {
    val witness = dssWitness("inlined", "SEQUENTIAL")
    val invariants =
      Regex("""line: (\d+)\s+column: \d+\s+value: '(.*?)'\s+format""", RegexOption.DOT_MATCHES_ALL)
        .findAll(witness)
        .map { it.groupValues[1].toInt() to it.groupValues[2] }
        .toList()
    assertTrue(invariants.isNotEmpty()) { witness }
    for ((line, value) in invariants) {
      // `check` spans lines 4-9 of inlined.c, `main` lines 11-19
      val foreign = if (line < 10) listOf("x", "n") else listOf("c", "d")
      assertTrue(foreign.none { Regex("""\b$it\b""").containsMatchIn(value) }) { witness }
    }
    assertTrue(verdictWithWitness("inlined", witness).contains("SafetyResult Safe"))
  }

  /**
   * Bit-vector terms do not print as C with their meaning, so their conjuncts are left out. Not
   * validated: the STABLE portfolio does not terminate on this unbounded loop.
   */
  @Test
  fun `a SAFE run over bit-vectors still writes a correctness witness`() {
    val witness = dssWitness("bitwise", "SEQUENTIAL")
    assertTrue(witness.contains("entry_type: 'invariant_set'")) { witness }
  }

  /** Each worker process only knows its own blocks, so the trace is stitched from all of them. */
  @Test
  fun `an UNSAFE run of the process executor writes a stitched violation witness`() {
    val witness = dssWitness("loop_unsafe", "PROCESS")
    assertTrue(witness.contains("entry_type: 'violation_sequence'")) { witness }
    assertTrue(witness.contains("\\result == 3")) { witness }
    assertTrue(witness.contains("type: 'target'")) { witness }
    assertTrue(verdictWithWitness("loop_unsafe", witness).contains("SafetyResult Unsafe"))
  }

  /** The complements of the backward invariants must hold at every reachable state. */
  @Test
  fun `a SAFE backward run writes location invariants that Theta validates`() {
    val witness = dssWitness("loop", "SEQUENTIAL", "--dss-direction", "BACKWARD")
    assertTrue(witness.contains("entry_type: 'invariant_set'")) { witness }
    assertTrue(verdictWithWitness("loop", witness).contains("SafetyResult Safe"))
  }

  @ParameterizedTest
  @ValueSource(strings = ["BACKWARD", "BIDIRECTIONAL"])
  fun `an UNSAFE run of a new direction writes a violation witness that Theta validates`(
    direction: String
  ) {
    val witness = dssWitness("loop_unsafe", "SEQUENTIAL", "--dss-direction", direction)
    assertTrue(witness.contains("entry_type: 'violation_sequence'")) { witness }
    assertTrue(witness.contains("type: 'target'")) { witness }
    assertTrue(verdictWithWitness("loop_unsafe", witness).contains("SafetyResult Unsafe"))
  }

  /** The verdict line of a DSS run on [program] against `<property>.prp`. */
  private fun dssVerdict(
    program: String,
    vararg options: String,
    property: String = "unreach-call",
  ): String {
    val (output, thrown) = runDss(program, *options, property = property)
    if (thrown != null) throw AssertionError(output, thrown)
    return output.lines().lastOrNull { it.contains("SafetyResult") }.orEmpty()
  }

  /** The output of a DSS run on [program] against `<property>.prp`, and what it threw. */
  private fun runDss(
    program: String,
    vararg options: String,
    property: String = "unreach-call",
    debug: Boolean = true,
  ): Pair<String, Throwable?> {
    val temp = createTempDirectory()
    val captured = temp.resolve("stdout_stderr").toFile()
    var thrown: Throwable? = null
    try {
      PrintStream(BufferedOutputStream(FileOutputStream(captured)), true).use { ps ->
        val savedOut = System.out
        val savedErr = System.err
        System.setOut(ps)
        System.setErr(ps)
        try {
          runCli(
            arrayOf(
              "--backend",
              "DSS",
              *options,
              "--property",
              javaClass.getResource("/c/dss/$property.prp")!!.path,
              "--output-directory",
              temp.absolutePathString(),
              "--input",
              javaClass.getResource("/c/dss/$program.c")!!.path,
              "--stacktrace",
              *(if (debug) arrayOf("--debug") else emptyArray()),
            )
          )
        } catch (e: Exception) {
          thrown = e
        } finally {
          System.setOut(savedOut)
          System.setErr(savedErr)
        }
      }
      return captured.readText() to thrown
    } finally {
      temp.toFile().deleteRecursively()
    }
  }

  /** The SV-COMP witness of a DSS run on [program] with emergent27's settings and [options]. */
  private fun dssWitness(
    program: String,
    executor: String,
    vararg options: String,
    checkers: String? = null,
  ): String {
    // BIDIRECTIONAL accepts a bounded checker only as the finisher
    val backends = checkers ?: if ("BIDIRECTIONAL" in options) "CEGAR" else "CEGAR,KIND"
    val temp = createTempDirectory()
    try {
      runCli(
        arrayOf(
          "--svcomp",
          "--backend",
          "DSS",
          *options,
          "--dss-executor",
          executor,
          "--dss-decomposition",
          "MIN_CUT_ABSORB_SELF_LOOPS",
          "--dss-checker-backends",
          backends,
          "--dss-checker-selection",
          "PRIORITY",
          "--property",
          javaClass.getResource("/c/dss/unreach-call.prp")!!.path,
          "--output-directory",
          temp.absolutePathString(),
          "--input",
          javaClass.getResource("/c/dss/$program.c")!!.path,
          "--stacktrace",
        )
      )
      return temp.resolve("witness.yml").toFile().readText()
    } finally {
      temp.toFile().deleteRecursively()
    }
  }

  /** The verdict line of the STABLE portfolio on [program] restricted by [witness]. */
  private fun verdictWithWitness(program: String, witness: String): String {
    val temp = createTempDirectory()
    val witnessFile = temp.resolve("witness.yml").toFile().apply { writeText(witness) }
    val captured = temp.resolve("stdout_stderr").toFile()
    try {
      PrintStream(BufferedOutputStream(FileOutputStream(captured)), true).use { ps ->
        val savedOut = System.out
        System.setOut(ps)
        try {
          runCli(
            arrayOf(
              "--svcomp",
              "--portfolio",
              "STABLE",
              "--property",
              javaClass.getResource("/c/dss/unreach-call.prp")!!.path,
              "--witness",
              witnessFile.absolutePath,
              "--output-directory",
              temp.resolve("validation").absolutePathString(),
              "--input",
              javaClass.getResource("/c/dss/$program.c")!!.path,
            )
          )
        } finally {
          System.setOut(savedOut)
        }
      }
      return captured.readLines().lastOrNull { it.contains("SafetyResult") }.orEmpty()
    } finally {
      temp.toFile().deleteRecursively()
    }
  }
}

/**
 * `XcfaCli.main` in this JVM. The CLI sets global pass switches from its config and, as a process
 * would exit, never resets them; later tests here would build their XCFAs with them.
 */
private fun runCli(args: Array<String>) {
  val lbe = LbePass.defaultLevel
  val coi = StaticCoiPass.enabled
  val ptrSize = PtrSizeToMemoryPass.enabled
  val dataRace = DataRaceToReachabilityPass.enabled
  val spinLoops = SpinLoopEffectPass.ENABLED
  val few = FetchExecuteWriteback.enabled
  try {
    XcfaCli.main(args)
  } finally {
    LbePass.defaultLevel = lbe
    StaticCoiPass.enabled = coi
    PtrSizeToMemoryPass.enabled = ptrSize
    DataRaceToReachabilityPass.enabled = dataRace
    SpinLoopEffectPass.ENABLED = spinLoops
    FetchExecuteWriteback.enabled = few
  }
}
