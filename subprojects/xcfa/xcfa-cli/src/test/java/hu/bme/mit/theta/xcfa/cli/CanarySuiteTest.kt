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
import java.util.concurrent.TimeUnit
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.junit.jupiter.api.fail

/**
 * The canary suite, as ordinary JUnit tests.
 *
 * `benchmark-results/canaries/run_canaries.sh` runs a sample of real SV-COMP tasks and a set of
 * feature-guard fixtures against a built `Theta-svcomp` distribution. It has been the gate for every
 * frontend change for months, but it lived entirely outside Gradle, so it was only ever run by
 * someone remembering to run it. This turns each of its rows into a test, which is what makes a
 * green build mean something.
 *
 * **The script is invoked, not reimplemented.** It already carries the parallelism, the mode
 * handling and -- more importantly -- the traps learned the hard way: a distribution auto-extracted
 * from the zip when the directory is stale, the exec bit on `theta-start.sh`, and the fact that a
 * `timeout` around `theta-start.sh` does not kill the JVM it spawns. Rewriting that in Kotlin would
 * mean rediscovering all of it. The script runs once and every result row becomes one dynamic test,
 * so a failure names the task that failed rather than "the suite exited 1".
 *
 * **It skips rather than fails when it cannot run.** The suite needs a built distribution and a
 * local sv-benchmarks checkout, neither of which exists on a fresh clone or in a sandboxed CI job.
 * A missing prerequisite is not evidence of a defect, so it is an assumption failure (skip), never a
 * test failure. What it must never do is pass silently, so an empty result set is a failure.
 *
 * Not wired into `test`: a parse-mode sweep is ~20 minutes and needs several gigabytes of
 * benchmarks. It is registered as its own task -- `./gradlew :theta-xcfa-cli:canaryTest` -- and
 * `test` explicitly excludes it.
 *
 * One row is flaky on a memory-constrained machine: `neural-networks/cartpole_0_safe` is large
 * enough to be OOM-killed, reported here as `nonzero exit 137`. Measured on a host with ~13 GB of
 * 62 free (the rest in use by other tenants), it failed at the default parallelism and at
 * `-Ptheta.canary.jobs=2`, and passed only at `PARALLEL_JOBS=1` -- and even alone it has failed
 * before. So it is the machine's free memory that decides, not the parallelism; `theta.canary.jobs`
 * lowers the pressure but is not a reliable remedy for it.
 *
 * It is deliberately NOT special-cased. A test that swallows `exit 137` would also swallow a genuine
 * memory regression, which is exactly the kind of thing this suite exists to catch.
 */
class CanarySuiteTest {

    private companion object {
        /** Rows look like `PASS     c/foo/bar.yml   unreach-call   ILP32  ok` (space-padded). */
        val CANARY_ROW =
            Regex("""^(PASS|FAIL|ERROR|UNKNOWN|TIMEOUT)\s+(\S+)\s+(\S+)\s+(\S+)\s*(.*)$""")

        /** Fixture rows look like `PASS  some_fixture.c   [b94       ] what it guards`. */
        val FIXTURE_ROW = Regex("""^(PASS|FAIL)\s+(\S+\.c)\s+\[([^]]*)]\s*(.*)$""")

        /** The suite is a sweep over hundreds of tasks; it is minutes, not seconds. */
        const val TIMEOUT_MINUTES = 90L
    }

    @TestFactory
    fun canarySuite(): List<DynamicTest> {
        val repoRoot = File(System.getProperty("theta.canary.repoRoot") ?: ".").absoluteFile
        val script = File(repoRoot, "benchmark-results/canaries/run_canaries.sh")
        val mode = System.getProperty("theta.canary.mode") ?: "parse"
        val distDir = System.getProperty("theta.canary.dist")?.let(::File)
        val svBenchmarks =
            File(System.getProperty("theta.canary.svBenchmarks") ?: repoRoot.resolveSibling("sv-benchmarks").path)

        assumeTrue(script.canExecute(), "canary script not present or not executable: $script")
        assumeTrue(svBenchmarks.isDirectory, "sv-benchmarks checkout not found at $svBenchmarks")
        assumeTrue(
            distDir == null || distDir.isDirectory || File(distDir.parentFile, "${distDir.name}.zip").isFile,
            "no built distribution at $distDir (run buildArchiveTheta-svcomp first)",
        )

        val command = buildList {
            add(script.absolutePath)
            add(distDir?.absolutePath ?: "")
            add(mode)
        }
        val process =
            ProcessBuilder(command)
                .directory(script.parentFile)
                .redirectErrorStream(true)
                .apply { environment()["SV_BENCHMARKS_ROOT"] = svBenchmarks.absolutePath }
                .start()
        val output = process.inputStream.bufferedReader().readText()
        if (!process.waitFor(TIMEOUT_MINUTES, TimeUnit.MINUTES)) {
            process.destroyForcibly()
            return listOf(
                DynamicTest.dynamicTest("canary suite") {
                    fail("the canary suite did not finish within $TIMEOUT_MINUTES minutes")
                }
            )
        }

        val tests = mutableListOf<DynamicTest>()
        var inFixtures = false
        for (line in output.lineSequence()) {
            if (line.startsWith("=== feature-guard fixtures")) {
                inFixtures = true
                continue
            }
            val row = (if (inFixtures) FIXTURE_ROW else CANARY_ROW).matchEntire(line.trimEnd()) ?: continue
            val status = row.groupValues[1]
            val name =
                if (inFixtures) "fixture ${row.groupValues[2]}"
                else "${row.groupValues[2]} [${row.groupValues[3]}]"
            val detail = row.groupValues.last()
            tests.add(
                DynamicTest.dynamicTest(name) {
                    // UNKNOWN and TIMEOUT are not passes: the suite is a gate, and a task that
                    // stopped producing its expected answer is exactly what it exists to catch.
                    if (status != "PASS") fail("$status -- $detail")
                }
            )
        }

        // An empty result set means the script produced nothing parseable -- a broken invocation
        // looks identical to a clean sweep otherwise, which is the one outcome this must not allow.
        if (tests.isEmpty()) {
            return listOf(
                DynamicTest.dynamicTest("canary suite") {
                    fail("the canary suite produced no parseable results:\n${output.take(4000)}")
                }
            )
        }
        return tests
    }
}
