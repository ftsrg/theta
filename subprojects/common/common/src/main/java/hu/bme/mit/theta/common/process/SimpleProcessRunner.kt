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
package hu.bme.mit.theta.common.process

import com.zaxxer.nuprocess.NuAbstractProcessHandler
import com.zaxxer.nuprocess.NuProcessBuilder
import java.nio.ByteBuffer
import java.util.concurrent.TimeUnit

object SimpleProcessRunner {

  fun run(cmd: String, timeout: Long = 0): String {
    val processBuilder = NuProcessBuilder(cmd.split(" "))
    val handler = ProcessHandler()
    processBuilder.setProcessListener(handler)
    processBuilder.start().waitFor(timeout, TimeUnit.SECONDS)
    return handler.output
  }

  class ProcessHandler : NuAbstractProcessHandler() {
    var output: String = ""
    var error: String = ""

    override fun onStdout(buffer: ByteBuffer?, closed: Boolean) {
      if (!closed && buffer != null) {
        val bytes = ByteArray(buffer.remaining())
        buffer[bytes]
        output = String(bytes)
      }
    }

    override fun onStderr(buffer: ByteBuffer?, closed: Boolean) {
      if (!closed && buffer != null) {
        val bytes = ByteArray(buffer.remaining())
        buffer[bytes]
        error = "$error\n${String(bytes)}"
      }
    }

    override fun onExit(statusCode: Int) {
      if (statusCode == Integer.MIN_VALUE) {
        throw ProcessException("Nuprocess launch error")
      }
      if (statusCode != 0) {
        throw ProcessException(
          if (error != "") error else "Process exit with non-zero code: $statusCode"
        )
      }
    }
  }
}

class ProcessException(err: String) : Exception(err)
