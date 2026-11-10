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
package hu.bme.mit.theta.xcfa.analysis.dss.actor

/** The analysis of a [DssBlockActor], without routing. */
interface DssBlockBehavior {

  fun initialMessages(): Collection<DssMessage>

  fun onPostCondition(message: DssPostConditionMessage): Collection<DssMessage>

  fun onViolationCondition(message: DssViolationConditionMessage): Collection<DssMessage>

  fun onRestriction(message: DssRestrictionMessage): Collection<DssMessage> = emptyList()

  /** Ignoring a conjecture would leave another block's assumption of it unchecked. */
  fun onConjecture(message: DssConjectureMessage): Collection<DssMessage> =
    throw UnsupportedOperationException("${javaClass.simpleName} cannot check conjectures")

  fun onMayViolation(message: DssMayViolationMessage): Collection<DssMessage> =
    throw UnsupportedOperationException("${javaClass.simpleName} cannot check conjectures")

  fun witness(): DssBlockWitness? = null

  /** Counters for the block's `STATISTIC` message. */
  fun statistics(): Map<String, String> = emptyMap()
}

/** The counters of a [PredicateBlockBehavior]. */
class DssBlockStatistics {
  var analyses = 0
  var violationConditionsReceived = 0
  var violationConditionsSent = 0
  var largestViolationCondition = 0
  var probes = 0
  var probesRefuted = 0
  var probesFailed = 0
  var conjectures = 0
  var mayAnalyses = 0
  var mayViolationsSent = 0
  var conjectureFailures = 0
  var quantifiedFormulas = 0

  fun toMap(): Map<String, String> =
    linkedMapOf(
        "analyses" to analyses,
        "vcReceived" to violationConditionsReceived,
        "vcSent" to violationConditionsSent,
        "vcMaxAtoms" to largestViolationCondition,
        "probes" to probes,
        "probesRefuted" to probesRefuted,
        "probesFailed" to probesFailed,
        "conjectures" to conjectures,
        "mayAnalyses" to mayAnalyses,
        "mayVcSent" to mayViolationsSent,
        "conjectureFailures" to conjectureFailures,
        "quantified" to quantifiedFormulas,
      )
      .mapValues { it.value.toString() }
}
