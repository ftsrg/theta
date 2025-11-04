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
package hu.bme.mit.theta.xcfa.cli.checkers

import com.zaxxer.nuprocess.NuAbstractProcessHandler
import com.zaxxer.nuprocess.NuProcess
import com.zaxxer.nuprocess.NuProcessBuilder
import hu.bme.mit.theta.analysis.EmptyCex
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.cli.XcfaCli
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.CachingFileSerializer
import hu.bme.mit.theta.xcfa.cli.utils.getGson
import hu.bme.mit.theta.xcfa.model.XCFA
import java.io.File
import java.lang.System.err
import java.nio.ByteBuffer
import java.util.*
import java.util.concurrent.TimeUnit
import kotlin.io.path.createTempDirectory

class InProcessChecker<F : SpecFrontendConfig, B : SpecBackendConfig>(
  val xcfa: XCFA?,
  val config: XcfaConfig<F, B>,
  val parseContext: ParseContext?,
  val logger: Logger,
) : SafetyChecker<EmptyProof, EmptyCex, XcfaPrec<*>> {

  override fun check(prec: XcfaPrec<*>?): SafetyResult<EmptyProof, EmptyCex> {
    return check()
  }

  override fun check(): SafetyResult<EmptyProof, EmptyCex> {
    val tempDir = createTempDirectory(config.outputConfig.resultFolder.toPath())
    Runtime.getRuntime()
      .addShutdownHook(
        Thread {
          if (tempDir.toFile().exists()) {
            tempDir.toFile().deleteRecursively()
          }
        }
      )

    val configJson =
      if (config.backendConfig.parseInProcess) {

        val config =
          config.copy(
            outputConfig = config.outputConfig.copy(resultFolder = tempDir.toFile()),
            backendConfig = config.backendConfig.copy(inProcess = false, timeoutMs = 0),
          )
        CachingFileSerializer.serialize("config.json", config) { getGson().toJson(config) }
      } else {
        xcfa!!
        parseContext!!
        val xcfaJson =
          CachingFileSerializer.serialize("xcfa.json", xcfa) { getGson(xcfa).toJson(xcfa) }
        val parseContextJson =
          CachingFileSerializer.serialize("parseContext.json", parseContext) {
            getGson(xcfa).toJson(parseContext)
          }

        val config =
          config.copy(
            inputConfig = config.inputConfig.copy(input = xcfaJson, parseCtx = parseContextJson),
            frontendConfig = config.frontendConfig.copy(inputType = InputType.JSON),
            backendConfig = config.backendConfig.copy(inProcess = false, timeoutMs = 0),
            outputConfig =
              config.outputConfig.copy(
                resultFolder = tempDir.toFile(),
                cOutputConfig = COutputConfig(enabled = false),
                xcfaOutputConfig = XcfaOutputConfig(enabled = false),
                chcOutputConfig = ChcOutputConfig(enabled = false),
                argConfig =
                  config.outputConfig.argConfig.copy(
                    enabled = true
                  ), // we need the arg to be produced
              ),
            // TODO is it good this way? I just updated mechanically but it does not sound good when
            // we need to produce a witness in a portfolio
          )
        CachingFileSerializer.serialize("config.json", config) { getGson(xcfa).toJson(config) }
      }

    val heapSize =
      "-Xmx${if(config.backendConfig.memlimit == 0L) 1420L else config.backendConfig.memlimit/1024/1024 }m"
    logger.write(Logger.Level.INFO, "Starting process with $heapSize of heap\n")

    val pb =
      NuProcessBuilder(
        listOf(
            ProcessHandle.current().info().command().orElse("java"),
            "-Xss120m",
            heapSize,
            heapSize,
            "-cp",
            File(XcfaCli::class.java.protectionDomain.codeSource.location.toURI()).absolutePath,
            XcfaCli::class.qualifiedName,
            "-c",
            configJson.absolutePath,
          )
          .filterNotNull()
      )
    val processHandler = ProcessHandler()
    pb.setProcessListener(processHandler)
    val process: NuProcess = pb.start()
    pb.environment().putAll(System.getenv())

    val retCode = process.waitFor(config.backendConfig.timeoutMs, TimeUnit.MILLISECONDS)
    val booleanSafetyResult =
      if (retCode == Int.MIN_VALUE) {
        if (processHandler.safetyResult == null) {
          process.destroy(true)
          throw ErrorCodeException(ExitCodes.TIMEOUT.code)
        } else {
          logger.write(
            Logger.Level.RESULT,
            "Config timed out but started writing result, trying to wait an additional 10%...",
          )
          val retCode = process.waitFor(config.backendConfig.timeoutMs / 10, TimeUnit.MILLISECONDS)
          if (retCode != 0) {
            throw ErrorCodeException(retCode)
          } else {
            processHandler.safetyResult
          }
        }
      } else if (retCode != 0) {
        throw ErrorCodeException(retCode)
      } else {
        processHandler.safetyResult
      }

    tempDir.toFile().listFiles()?.forEach {
      it.copyTo(config.outputConfig.resultFolder.resolve(it.name), overwrite = true)
    }
    tempDir.toFile().deleteRecursively()

    return booleanSafetyResult as SafetyResult<EmptyProof, EmptyCex>
  }

  private class ProcessHandler : NuAbstractProcessHandler() {

    private val stdout = LinkedList<String>()
    private var stdoutRemainder = ""
    private val stderr = LinkedList<String>()
    private var stderrRemainder = ""
    var safetyResult: SafetyResult<*, *>? = null
      private set

    override fun onStdout(buffer: ByteBuffer, closed: Boolean) {
      if (!closed) {
        val bytes = ByteArray(buffer.remaining())
        buffer[bytes]
        val str = bytes.decodeToString()

        stdoutRemainder += str
        if (stdoutRemainder.contains("SafetyResult Safe")) {
          safetyResult = SafetyResult.safe<EmptyProof, EmptyCex>(EmptyProof.getInstance())
        }
        if (stdoutRemainder.contains("SafetyResult Unsafe")) {
          safetyResult = SafetyResult.unsafe(EmptyCex.getInstance(), EmptyProof.getInstance())
        }
        if (stdoutRemainder.contains("SafetyResult Unknown")) {
          safetyResult = SafetyResult.unknown<EmptyProof, EmptyCex>()
        }

        val newLines = stdoutRemainder.split("\n") // if ends with \n, last element will be ""
        newLines.subList(0, newLines.size - 1).forEach {
          stdout.add(it)
          println("server: $it")
        }
        stdoutRemainder = newLines[newLines.size - 1]
      }
    }

    override fun onStderr(buffer: ByteBuffer, closed: Boolean) {
      if (!closed) {
        val bytes = ByteArray(buffer.remaining())
        buffer[bytes]
        val str = bytes.decodeToString()

        stderrRemainder += str

        val newLines = stderrRemainder.split("\n") // if ends with \n, last element will be ""
        newLines.subList(0, newLines.size - 1).forEach {
          stderr.add(it)
          err.println("server: $it")
        }
        stderrRemainder = newLines[newLines.size - 1]
      }
    }
  }
}
