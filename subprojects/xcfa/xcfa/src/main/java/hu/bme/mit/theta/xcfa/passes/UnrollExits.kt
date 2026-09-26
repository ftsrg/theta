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
 * Unroll exit locations: where [UnrollPass] (with `markUnrollExits`) sends a continuation that an
 * unroll bound cut off, so that a backend can ask whether the bound was actually reached.
 *
 * An exit location is named after a key that identifies its cut point across unrolling rounds: the
 * procedure and the input location (loop head, recursive callee or back-edge target) it belongs to.
 * All copies of the same loop -- e.g. of an inner loop in each copy of the outer one -- share a
 * key, and with it a single exit location.
 */
object UnrollExits {

  enum class Kind(internal val tag: String, val deepenable: Boolean) {
    LOOP("loop", true),
    RECURSION("rec", true),
    /** A back edge of a loop the pass could not take apart: no bound governs how deep it goes. */
    BACK_EDGE("cut", false),
  }

  private const val PREFIX = "__unroll_exit__"

  /**
   * Ends the key in a location name: copies of an exit location get suffixes (a counter when a
   * procedure body is spliced in, `_<pid>` in the per-thread copies), which must not change its
   * key.
   */
  private const val END = '$'

  fun key(kind: Kind, procedure: String, name: String): String = "${kind.tag}_${procedure}_$name"

  fun locationName(key: String): String = "$PREFIX$key$END"

  /** The key of the exit location [loc] (or of a copy of one), or null if it is not one. */
  fun keyOf(loc: XcfaLocation): String? =
    loc.name
      .takeIf { it.startsWith(PREFIX) && END in it }
      ?.let { it.substring(PREFIX.length, it.lastIndexOf(END)) }

  fun kindOf(key: String): Kind = Kind.entries.first { key.startsWith("${it.tag}_") }
}
