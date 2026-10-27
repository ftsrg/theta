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
package hu.bme.mit.theta.common.process

import com.zaxxer.nuprocess.NuProcess
import com.zaxxer.nuprocess.NuProcessBuilder
import com.zaxxer.nuprocess.NuProcessHandler
import hu.bme.mit.theta.common.NativeImage
import java.io.InputStream
import java.nio.ByteBuffer
import java.util.concurrent.TimeUnit
import kotlin.concurrent.thread

/**
 * Starts processes with NuProcess, except in a GraalVM native image: NuProcess forks through
 * libjava, which a native image does not have, so there a [java.lang.Process] drives the handler.
 */
object NuProcesses {

  @JvmStatic
  @JvmOverloads
  fun start(
    command: List<String>,
    handler: NuProcessHandler,
    environment: Map<String, String> = emptyMap(),
  ): NuProcess? =
    if (NativeImage.running) PlainProcess(command, environment, handler)
    else
      NuProcessBuilder(command)
        .also {
          it.environment().putAll(environment)
          it.setProcessListener(handler)
        }
        .start()
}

/** The calls NuProcess makes on its handler, made by threads that read the process's output. */
private class PlainProcess(
  command: List<String>,
  environment: Map<String, String>,
  private var handler: NuProcessHandler,
) : NuProcess {
  private val process: Process
  private val exit: Thread

  init {
    handler.onPreStart(this)
    process = ProcessBuilder(command).also { it.environment().putAll(environment) }.start()
    handler.onStart(this)
    val readers =
      listOf(
        pump(process.inputStream) { buffer, closed -> handler.onStdout(buffer, closed) },
        pump(process.errorStream) { buffer, closed -> handler.onStderr(buffer, closed) },
      )
    exit =
      thread(isDaemon = true) {
        val code = process.waitFor()
        readers.forEach { it.join() }
        handler.onExit(code)
      }
  }

  private fun pump(stream: InputStream, sink: (ByteBuffer, Boolean) -> Unit) =
    thread(isDaemon = true) {
      val bytes = ByteArray(NuProcess.BUFFER_CAPACITY)
      stream.use {
        while (true) {
          val n = it.read(bytes)
          if (n < 0) break
          sink(ByteBuffer.wrap(bytes, 0, n), false)
        }
      }
      sink(ByteBuffer.allocate(0), true)
    }

  override fun waitFor(timeout: Long, timeUnit: TimeUnit): Int {
    if (timeout == 0L) exit.join() else exit.join(timeUnit.toMillis(timeout))
    return if (exit.isAlive) Int.MIN_VALUE else process.exitValue()
  }

  @Synchronized
  override fun wantWrite() {
    val buffer = ByteBuffer.allocate(NuProcess.BUFFER_CAPACITY)
    do {
      buffer.clear()
      val more = handler.onStdinReady(buffer)
      process.outputStream.write(buffer.array(), buffer.position(), buffer.remaining())
      process.outputStream.flush()
    } while (more)
  }

  @Synchronized
  override fun writeStdin(buffer: ByteBuffer) {
    val bytes = ByteArray(buffer.remaining())
    buffer.get(bytes)
    process.outputStream.write(bytes)
    process.outputStream.flush()
  }

  override fun closeStdin(force: Boolean) = process.outputStream.close()

  override fun hasPendingWrites() = false

  override fun destroy(force: Boolean) {
    process.descendants().forEach { if (force) it.destroyForcibly() else it.destroy() }
    if (force) process.destroyForcibly() else process.destroy()
  }

  override fun isRunning() = process.isAlive

  override fun setProcessHandler(processHandler: NuProcessHandler) {
    handler = processHandler
  }

  override fun getPID() = process.pid().toInt()
}
