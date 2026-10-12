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
package hu.bme.mit.theta.xcfa.dss.actor

/**
 * Diagnostic trace of a DSS run (`--dss-trace`): one line per processed message and per block
 * analysis try, each written when it starts and when it ends, so the last lines of a run killed by
 * a timeout show what it was doing. Off ([sink] `null`) unless the CLI sets it; process-wide, as
 * there is one DSS run per process.
 *
 * Line format: `DSS-TRACE <ms since enable> <event> key=value...`.
 */
object DssTrace {

  @Volatile private var sink: ((String) -> Unit)? = null
  private var startNanos = 0L

  fun enable(sink: (String) -> Unit) {
    startNanos = System.nanoTime()
    this.sink = sink
  }

  fun disable() {
    sink = null
  }

  val enabled: Boolean
    get() = sink != null

  fun event(name: String, vararg fields: Pair<String, Any?>) {
    val sink = sink ?: return
    val ms = (System.nanoTime() - startNanos) / 1_000_000
    sink(
      buildString {
        append("DSS-TRACE ").append(ms).append(' ').append(name)
        fields.forEach { (k, v) -> append(' ').append(k).append('=').append(v) }
      }
    )
  }

  /** Traces [name]-start and [name]-end (with duration and outcome) around [action]. */
  inline fun <T> span(
    name: String,
    vararg fields: Pair<String, Any?>,
    outcome: (T) -> Any? = { "ok" },
    action: () -> T,
  ): T {
    if (!enabled) return action()
    val start = System.nanoTime()
    event("$name-start", *fields)
    val result =
      try {
        action()
      } catch (e: Throwable) {
        event(
          "$name-end",
          *fields,
          "ms" to (System.nanoTime() - start) / 1_000_000,
          "outcome" to "exception:${e.javaClass.simpleName}",
        )
        throw e
      }
    event(
      "$name-end",
      *fields,
      "ms" to (System.nanoTime() - start) / 1_000_000,
      "outcome" to outcome(result),
    )
    return result
  }
}
