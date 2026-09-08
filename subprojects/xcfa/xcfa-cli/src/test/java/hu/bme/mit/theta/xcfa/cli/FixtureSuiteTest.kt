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
import java.util.zip.ZipFile
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.junit.jupiter.api.fail

/**
 * The feature-guard fixtures, as ordinary JUnit tests.
 *
 * Each fixture under `canaries/fixtures` is a minimal program isolating one frontend or
 * instrumentation change, and `fixtures/fixtures.tsv` says how to run it and what must happen:
 * - `PARSE-OK` / `FRONTEND-FAIL` -- run the frontend only (`--backend NONE`) and check whether it
 *   built the XCFA. A fixture builds only if its change is present, so reverting the change flips
 *   the outcome.
 * - `SAFE` / `UNSAFE`, optionally `:<property>` -- run the real verifier and check the verdict. Use
 *   these for changes that alter values rather than what parses: a miswritten memory cell parses
 *   perfectly and only shows up as a wrong answer.
 *
 * Unlike [CanarySuiteTest] this **fails** rather than skips when its prerequisites are missing: the
 * fixtures are the part of the gate that must run everywhere, and a silent skip would let a change
 * through unguarded. It never fetches sv-benchmarks; it only says where it looked.
 */
class FixtureSuiteTest {

  private companion object {
    /** Frontend-only fixtures are parsing, not verification. */
    val PARSE_TIMEOUT_SECONDS = seconds("theta.fixture.parseTimeout", 90L)

    /** Verdict fixtures run the portfolio; keep them small enough to stay under this. */
    val VERDICT_TIMEOUT_SECONDS = seconds("theta.fixture.verdictTimeout", 180L)

    private fun seconds(property: String, fallback: Long) =
      System.getProperty(property)?.toLongOrNull() ?: fallback
  }

  @TestFactory
  fun fixtures(): List<DynamicTest> {
    val repoRoot = File(System.getProperty("theta.canary.repoRoot") ?: ".").absoluteFile
    val home =
      System.getProperty("theta.canary.home")?.let(::File)
        ?: File(repoRoot, "subprojects/xcfa/xcfa-cli/canaries")
    val tsv = File(home, "fixtures/fixtures.tsv")
    val svBenchmarks =
      File(
        System.getProperty("theta.canary.svBenchmarks")
          ?: repoRoot.resolveSibling("sv-benchmarks").path
      )
    val properties = File(svBenchmarks, "c/properties")
    val distDir =
      System.getProperty("theta.canary.dist")?.let(::File)
        ?: File(repoRoot, "subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp")

    // Prerequisites are failures, not assumptions. Say exactly what is missing and how to get it;
    // never fetch anything.
    val missing =
      when {
        !tsv.isFile -> "no fixture registry at $tsv"
        !properties.isDirectory ->
          "sv-benchmarks checkout not found: expected the property files at $properties.\n" +
            "Check out https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks next to this " +
            "repository, or point -Ptheta.canary.svBenchmarks at an existing checkout. This task " +
            "never downloads it."
        else -> null
      }
    if (missing != null) return listOf(DynamicTest.dynamicTest("fixtures") { fail(missing) })

    val theta = ensureDistribution(distDir)
    if (theta == null) {
      return listOf(
        DynamicTest.dynamicTest("fixtures") {
          fail(
            "no built distribution at $distDir -- run `gradle :theta-xcfa-cli:buildArchiveTheta-svcomp` first"
          )
        }
      )
    }

    val rows =
      tsv
        .readLines()
        .drop(1)
        .filter { it.isNotBlank() }
        .map { it.split('\t') }
        .filter { it.size >= 4 }

    if (rows.isEmpty())
      return listOf(DynamicTest.dynamicTest("fixtures") { fail("no fixture rows in $tsv") })

    return rows.map { row ->
      val (fixture, arithmetic, architecture, expect) = row
      val feature = row.getOrElse(4) { "" }
      DynamicTest.dynamicTest("fixture $fixture") {
        val input = File(home, "fixtures/$fixture")
        check(input.isFile) { "fixture file not found: $input" }
        val actual = run(theta, input, arithmetic, architecture, expect, properties)
        if (actual != expect) fail("expected=$expect actual=$actual -- $feature")
      }
    }
  }

  /** The outcome of one fixture, in the vocabulary [fixtures.tsv] uses. */
  private fun run(
    theta: File,
    input: File,
    arithmetic: String,
    architecture: String,
    expect: String,
    properties: File,
  ): String {
    val verdict = expect.substringBefore(':')
    val isVerdictFixture = verdict == "SAFE" || verdict == "UNSAFE"
    val property =
      File(
        properties,
        if (expect.contains(':')) "${expect.substringAfter(':')}.prp" else "unreach-call.prp",
      )
    check(property.isFile) { "property file not found: $property" }

    val command = buildList {
      add(File(theta, "theta-start.sh").absolutePath)
      add(input.absolutePath)
      add("--svcomp")
      addAll(if (isVerdictFixture) listOf("--portfolio", "STABLE") else listOf("--backend", "NONE"))
      addAll(listOf("--loglevel", "RESULT"))
      addAll(listOf("--property", property.absolutePath))
      addAll(listOf("--architecture", architecture))
      addAll(listOf("--arithmetic", arithmetic))
    }
    val timeout = if (isVerdictFixture) VERDICT_TIMEOUT_SECONDS else PARSE_TIMEOUT_SECONDS
    val output = execute(command, theta, timeout)

    if (!isVerdictFixture) {
      return when {
        output.contains("ParsingResult Success") -> "PARSE-OK"
        output.contains("Frontend failed!") -> "FRONTEND-FAIL"
        else -> "OTHER"
      }
    }
    val actual =
      when {
        output.contains("(SafetyResult Safe)") -> "SAFE"
        output.contains("(SafetyResult Unsafe") -> "UNSAFE"
        else -> "OTHER"
      }
    // The expectation may name a property after the verdict; echo it back on a match so the
    // comparison is against the registry's own spelling.
    return if (actual == verdict) expect else actual
  }

  /**
   * Runs [command] and returns everything it printed.
   *
   * `theta-start.sh` launches a child JVM rather than exec'ing one, so killing the script on
   * timeout leaves that JVM running and holding the pipe -- the read would then block forever, long
   * after the timeout. Destroying the whole process tree is what actually releases it.
   */
  private fun execute(command: List<String>, workingDir: File, timeoutSeconds: Long): String {
    val process = ProcessBuilder(command).directory(workingDir).redirectErrorStream(true).start()
    // Drain on a thread of its own: the pipe has to keep moving while we wait, or a chatty run
    // fills it and blocks the child before the timeout can fire.
    val output = StringBuilder()
    val collector = Thread {
      process.inputStream.bufferedReader().forEachLine { output.appendLine(it) }
    }
    collector.isDaemon = true
    collector.start()
    if (!process.waitFor(timeoutSeconds, TimeUnit.SECONDS)) {
      process.descendants().forEach { it.destroyForcibly() }
      process.destroyForcibly()
      process.waitFor(10, TimeUnit.SECONDS)
      collector.join(10_000)
      return "$output\nTIMEOUT after ${timeoutSeconds}s"
    }
    collector.join(30_000)
    return output.toString()
  }

  /**
   * The extracted distribution, extracting the archive next to it when only that is present, or
   * null when neither exists. Also restores the exec bit, which a plain unzip drops.
   */
  private fun ensureDistribution(distDir: File): File? {
    val start = File(distDir, "theta-start.sh")
    if (!start.isFile) {
      val zip = File(distDir.parentFile, "${distDir.name}.zip")
      if (!zip.isFile) return null
      ZipFile(zip).use { archive ->
        archive.entries().asSequence().forEach { entry ->
          val target = File(distDir.parentFile, entry.name)
          if (entry.isDirectory) {
            target.mkdirs()
          } else {
            target.parentFile.mkdirs()
            archive.getInputStream(entry).use { input ->
              target.outputStream().use { output -> input.copyTo(output) }
            }
          }
        }
      }
    }
    if (!start.isFile) return null
    start.setExecutable(true)
    return distDir
  }
}
