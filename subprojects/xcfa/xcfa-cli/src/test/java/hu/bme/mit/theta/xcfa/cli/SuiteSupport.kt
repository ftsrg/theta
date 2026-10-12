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

/** What one task run produced, and whether it was cut short. */
internal data class RunResult(val output: String, val timedOut: Boolean)

/**
 * Plumbing shared by [CanarySuiteTest] and [FixtureSuiteTest].
 *
 * Both suites drive the packaged distribution over a TSV of tasks. Doing that here rather than in a
 * shell script keeps them runnable wherever the JVM is, and keeps one copy of the parts that are
 * easy to get subtly wrong: draining a chatty process, killing its whole tree on timeout, and
 * restoring the execute bits the zip does not carry.
 */
internal object SuiteSupport {

  /**
   * The extracted distribution, unpacking `<name>.zip` beside it when the directory is missing.
   *
   * A zip stores no POSIX permissions, so every launcher and solver binary arrives non-executable.
   * That turns into "Permission denied" from whichever solver a task happens to need -- which looks
   * like a broken build rather than a broken unpack -- so the execute bit is put back here.
   * `setExecutable` is a no-op on platforms without one.
   */
  fun ensureDistribution(distDir: File): File? {
    val launcher = File(distDir, "theta-start.sh")
    if (!launcher.isFile) {
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
    if (!File(distDir, "theta.jar").isFile) return null
    distDir
      .walkTopDown()
      .filter { it.isFile }
      .forEach { file ->
        if (file.extension == "sh" || file.isNativeExecutable()) file.setExecutable(true)
      }
    return distDir
  }

  /** ELF, Mach-O or PE magic -- the solver binaries the distribution ships per platform. */
  private fun File.isNativeExecutable(): Boolean =
    runCatching {
        inputStream().use { stream ->
          val magic = ByteArray(4)
          if (stream.read(magic) < 4) return false
          val elf = magic[0] == 0x7F.toByte() && magic[1].toInt().toChar() == 'E'
          val pe = magic[0].toInt().toChar() == 'M' && magic[1].toInt().toChar() == 'Z'
          val machO = magic[0] == 0xCF.toByte() || magic[0] == 0xCE.toByte()
          elf || pe || machO
        }
      }
      .getOrDefault(false)

  /**
   * The command that runs one task.
   *
   * The shipped `theta-start.sh` is the entry point SV-COMP itself uses, so prefer it and stay
   * faithful to how the tool is really invoked. Where there is no POSIX shell to run it, fall back
   * to the jar it would have launched.
   */
  fun thetaCommand(dist: File, input: File, options: List<String>): List<String> {
    val launcher = File(dist, "theta-start.sh")
    if (launcher.canExecute()) {
      return listOf(launcher.absolutePath, input.absolutePath) + options
    }
    val java = File(File(System.getProperty("java.home"), "bin"), "java").absolutePath
    return listOf(java, "-Xss120m", "-jar", File(dist, "theta.jar").absolutePath) +
      listOf("--input", input.absolutePath) +
      options +
      listOf("--smt-home", File(dist, "solvers").absolutePath)
  }

  /** Runs [command], returning everything it printed and whether it had to be killed. */
  fun execute(
    command: List<String>,
    workingDir: File,
    timeoutSeconds: Long,
    environment: Map<String, String> = emptyMap(),
  ): RunResult {
    val process =
      ProcessBuilder(command)
        .directory(workingDir)
        .redirectErrorStream(true)
        .apply { environment().putAll(environment) }
        .start()
    // Drain on a thread of its own: the pipe has to keep moving while we wait, or a chatty run
    // fills it and blocks the child before the timeout can fire.
    val output = StringBuilder()
    val collector = Thread {
      process.inputStream.bufferedReader().forEachLine { output.appendLine(it) }
    }
    collector.isDaemon = true
    collector.start()
    // theta-start.sh launches a child JVM rather than exec'ing one, so killing only the script
    // leaves that JVM holding the pipe and the read would block long past the timeout.
    if (!process.waitFor(timeoutSeconds, TimeUnit.SECONDS)) {
      process.descendants().forEach { it.destroyForcibly() }
      process.destroyForcibly()
      process.waitFor(10, TimeUnit.SECONDS)
      collector.join(10_000)
      return RunResult(output.toString(), timedOut = true)
    }
    collector.join(30_000)
    return RunResult(output.toString(), timedOut = false)
  }

  /**
   * Data rows of a TSV, keyed by column name.
   *
   * Looking columns up by name means any superset of the expected schema works unmodified, which is
   * what lets a filtered or annotated task list be fed to the same suite.
   */
  fun readTsv(file: File): List<Map<String, String>> {
    val lines = file.readLines().filter { it.isNotBlank() }
    if (lines.isEmpty()) return emptyList()
    val header = lines.first().split('\t')
    return lines.drop(1).map { line -> header.zip(line.split('\t')).toMap() }
  }
}
