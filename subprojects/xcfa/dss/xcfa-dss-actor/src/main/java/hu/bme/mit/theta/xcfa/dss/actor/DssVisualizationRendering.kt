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

private const val ANSI_RESET = "[0m"

private fun ansiColorFor(type: DssMessageType): String =
  when (type) {
    DssMessageType.POST_CONDITION -> "[32m" // green
    DssMessageType.VIOLATION_CONDITION -> "[33m" // yellow
    DssMessageType.EXCEPTION -> "[1;31m" // bold red
    DssMessageType.RESULT -> "[1;35m" // bold magenta
    DssMessageType.STATISTIC -> "[34m" // blue
  }

private fun payloadSummary(message: DssMessage): String? =
  when (message) {
    is DssPostConditionMessage -> message.postcondition?.toString()
    is DssViolationConditionMessage -> message.violationCondition?.toString()
    is DssExceptionMessage -> message.error.message
    is DssResultMessage -> message.result.toString()
    is DssStatisticsMessage -> message.stats.takeIf { it.isNotEmpty() }?.toString()
  }

private fun DssLogEntry.render(startMillis: Long): String {
  val elapsedMillis = timestampMillis - startMillis
  val summary = payloadSummary(message)
  val head = "[+${elapsedMillis}ms] ${message.senderId} -> ${message.type}"
  return if (summary != null) "$head: $summary" else head
}

fun DssVisualizationActor.renderTextLog(): String {
  val entries = log
  if (entries.isEmpty()) return ""
  val startMillis = entries.first().timestampMillis
  return entries.joinToString("\n") { it.render(startMillis) }
}

fun DssVisualizationActor.renderAnsiColoredLog(): String {
  val entries = log
  if (entries.isEmpty()) return ""
  val startMillis = entries.first().timestampMillis
  return entries.joinToString("\n") { entry ->
    "${ansiColorFor(entry.message.type)}${entry.render(startMillis)}$ANSI_RESET"
  }
}
