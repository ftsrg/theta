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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.xcfa.model.XcfaLocation

/**
 * Locations where [UnrollPass] sends the continuations an unroll bound cuts off. Their names carry
 * a key identifying the cut point (procedure and input location) across unrolling rounds.
 */
object UnrollExits {

  enum class Kind(internal val tag: String, val deepenable: Boolean) {
    LOOP("loop", true),
    RECURSION("rec", true),
    // a back edge of a loop the pass could not take apart: no bound to deepen
    BACK_EDGE("cut", false),
  }

  private const val PREFIX = "__unroll_exit__"

  // ends the key: copies of an exit location get name suffixes (e.g. inlining counters, pids)
  private const val END = '$'

  fun key(kind: Kind, procedure: String, name: String): String = "${kind.tag}_${procedure}_$name"

  fun locationName(key: String): String = "$PREFIX$key$END"

  fun keyOf(loc: XcfaLocation): String? =
    loc.name
      .takeIf { it.startsWith(PREFIX) && END in it }
      ?.let { it.substring(PREFIX.length, it.lastIndexOf(END)) }

  fun kindOf(key: String): Kind = Kind.entries.first { key.startsWith("${it.tag}_") }
}
