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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.xcfa.ErrorDetection.*
import hu.bme.mit.theta.xcfa.XcfaProperty

class UnknownResultException(message: String = "Unknown analysis result") :
  RuntimeException(message)

/**
 * Derives the correct LTL property string for a given ErrorDetection type. Optionally inspects a
 * trace to disambiguate MEMSAFETY and MEMCLEANUP cases.
 */
fun XcfaProperty.ltlPropertyFromTrace(trace: Trace<XcfaState<*>, XcfaAction>?): String? {
  return when (this.inputProperty) {
    MEMSAFETY,
    MEMCLEANUP -> {
      val locName =
        trace
          ?.states
          ?.asReversed()
          ?.firstOrNull { it.processes.values.any { it.locs.any { it.name.contains("__THETA_") } } }
          ?.processes
          ?.values
          ?.firstOrNull { it.locs.any { it.name.contains("__THETA_") } }
          ?.locs
          ?.firstOrNull { it.name.contains("__THETA_") }
          ?.name

      locName?.let {
        when (it) {
          "__THETA_bad_free" -> MEMSAFETY.ltl(Companion.MemSafetyType.VALID_FREE)
          "__THETA_bad_deref" -> MEMSAFETY.ltl(Companion.MemSafetyType.VALID_DEREF)
          "__THETA_lost" ->
            if (this.inputProperty == MEMCLEANUP) {
              MEMCLEANUP.ltl(Unit)
            } else {
              throw UnknownResultException("Uncertain MEMSAFETY result: __THETA_lost encountered")
            }
          else -> throw RuntimeException("Could not determine subproperty from location name: $it")
        }
      }
    }

    DATA_RACE -> DATA_RACE.ltl(Unit)
    ERROR_LOCATION -> ERROR_LOCATION.ltl(Unit)
    OVERFLOW -> OVERFLOW.ltl(Unit)
    NO_ERROR -> NO_ERROR.ltl(Unit)
    TERMINATION -> TERMINATION.ltl(Unit)
  }
}
