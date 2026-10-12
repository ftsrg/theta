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
package hu.bme.mit.theta.xcfa.cli

import java.io.File
import java.util.concurrent.Executors
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.junit.jupiter.api.fail

/**
 * The canary suite: a sample of real SV-COMP tasks run against a built `Theta-svcomp`.
 *
 * `canaries/canaries.tsv` lists the tasks; each row becomes one dynamic test, so a failure names
 * the task rather than "the suite exited 1". Two modes:
 * - `parse` (default) -- frontend only (`--backend NONE`), checking that each task still builds an
 *   XCFA. Fast, and what guards frontend changes.
 * - `full` (`-Ptheta.canary.mode=full`) -- the real portfolio, comparing the verdict against the
 *   task's expected one. Minutes per task; use a filtered TSV.
 *
 * The feature-guard fixtures are their own task, [FixtureSuiteTest].
 *
 * **It skips rather than fails when it cannot run.** The suite needs a built distribution and a
 * local sv-benchmarks checkout, neither of which exists in a fresh clone or a sandboxed CI job. A
 * missing prerequisite is an assumption failure, never a test failure. It must not pass silently
 * either, so an empty task list is a failure.
 *
 * Not wired into `test`; run it with `gradle :theta-xcfa-cli:canaryTest`.
 *
 * Large canaries need several GB each, so on a memory-constrained machine one may be OOM-killed and
 * reported as a nonzero exit. That is deliberately not special-cased: a test that swallows it would
 * also swallow a genuine memory regression, which is what this suite exists to catch.
 */
class CanarySuiteTest {

  private companion object {
    /** Parsing only; a task that needs longer than this has regressed. */
    val PARSE_TIMEOUT_SECONDS = seconds("theta.canary.parseTimeout", 60L)

    /** Full mode runs the portfolio, which is allowed to think for a while. */
    val FULL_TIMEOUT_SECONDS = seconds("theta.canary.fullTimeout", 90L)

    /** Each task is a separate JVM needing several GB, so this is memory-bound, not CPU-bound. */
    val PARALLELISM = System.getProperty("theta.canary.jobs")?.toIntOrNull() ?: 4

    private fun seconds(property: String, fallback: Long) =
      System.getProperty(property)?.toLongOrNull() ?: fallback
  }

  private data class Outcome(val status: String, val detail: String)

  @TestFactory
  fun canarySuite(): List<DynamicTest> {
    val repoRoot = File(System.getProperty("theta.canary.repoRoot") ?: ".").absoluteFile
    val home =
      System.getProperty("theta.canary.home")?.let(::File)
        ?: File(repoRoot, "subprojects/xcfa/xcfa-cli/canaries")
    val tsv = System.getProperty("theta.canary.tsv")?.let(::File) ?: File(home, "canaries.tsv")
    val mode = System.getProperty("theta.canary.mode") ?: "parse"
    val svBenchmarks =
      File(
        System.getProperty("theta.canary.svBenchmarks")
          ?: repoRoot.resolveSibling("sv-benchmarks").path
      )
    val distDir =
      System.getProperty("theta.canary.dist")?.let(::File)
        ?: File(repoRoot, "subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp")

    check(mode == "parse" || mode == "full") { "mode must be 'parse' or 'full', got: $mode" }
    assumeTrue(tsv.isFile, "no canary registry at $tsv")
    assumeTrue(svBenchmarks.isDirectory, "sv-benchmarks checkout not found at $svBenchmarks")
    val dist = SuiteSupport.ensureDistribution(distDir)
    assumeTrue(
      dist != null,
      "no built distribution at $distDir (run `gradle :theta-xcfa-cli:buildArchiveTheta-svcomp`)",
    )

    val rows = SuiteSupport.readTsv(tsv)
    // A broken registry looks exactly like a clean sweep otherwise, which is the one outcome this
    // must not allow.
    if (rows.isEmpty()) {
      return listOf(DynamicTest.dynamicTest("canary suite") { fail("no task rows in $tsv") })
    }

    val pool = Executors.newFixedThreadPool(PARALLELISM)
    val outcomes =
      try {
        rows
          .map { row -> row to pool.submit<Outcome> { run(row, dist!!, svBenchmarks, mode) } }
          .map { (row, future) -> row to future.get() }
      } finally {
        pool.shutdown()
      }

    return outcomes.map { (row, outcome) ->
      val name = "${row["task_yml_relpath"]} [${row["property"]}]"
      DynamicTest.dynamicTest(name) {
        // UNKNOWN and TIMEOUT are not passes: the suite is a gate, and a task that stopped
        // producing its expected answer is exactly what it exists to catch.
        if (outcome.status != "PASS") fail("${outcome.status} -- ${outcome.detail}")
      }
    }
  }

  private fun run(row: Map<String, String>, dist: File, svBenchmarks: File, mode: String): Outcome {
    val input = File(svBenchmarks, row.getValue("input_file_relpath"))
    val property = File(svBenchmarks, row.getValue("property_file_relpath"))
    val dataModel = row.getValue("data_model")
    val expected = row.getValue("expected_verdict")

    val options = buildList {
      add("--svcomp")
      addAll(if (mode == "parse") listOf("--backend", "NONE") else listOf("--portfolio", "STABLE"))
      addAll(listOf("--loglevel", "RESULT"))
      addAll(listOf("--property", property.absolutePath))
      addAll(listOf("--architecture", dataModel))
    }
    val timeout = if (mode == "parse") PARSE_TIMEOUT_SECONDS else FULL_TIMEOUT_SECONDS
    val result =
      SuiteSupport.execute(SuiteSupport.thetaCommand(dist, input, options), dist, timeout)

    if (mode == "parse") {
      return when {
        result.timedOut -> Outcome("TIMEOUT", "parse timeout (${timeout}s)")
        result.output.contains("Frontend failed!") -> Outcome("FAIL", "Frontend failed!")
        result.output.contains("ParsingResult Success") -> Outcome("PASS", "ok")
        else -> Outcome("FAIL", "no ParsingResult Success in output")
      }
    }

    if (result.timedOut) return Outcome("TIMEOUT", "full timeout (${timeout}s)")
    val got =
      when {
        result.output.contains("(SafetyResult Safe)") -> "true"
        result.output.contains("(SafetyResult Unsafe") -> "false"
        result.output.contains("(SafetyResult Unknown)") -> "unknown"
        else -> "error"
      }
    return when (got) {
      expected -> Outcome("PASS", "expected=$expected got=$got")
      "unknown" -> Outcome("UNKNOWN", "expected=$expected got=$got")
      "error" -> Outcome("ERROR", "expected=$expected got=$got")
      else -> Outcome("FAIL", "expected=$expected got=$got")
    }
  }
}
