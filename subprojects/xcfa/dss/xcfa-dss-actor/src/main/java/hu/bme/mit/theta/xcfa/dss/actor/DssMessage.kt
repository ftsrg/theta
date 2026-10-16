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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import java.util.concurrent.atomic.AtomicLong

private val sequence = AtomicLong()

/**
 * Mirrors CPAchecker's `DssMessage.DssMessageType` - five types; the paper only describes the two
 * analysis messages (`post`, `vcond`).
 */
enum class DssMessageType {
  POST_CONDITION,
  VIOLATION_CONDITION,
  EXCEPTION,
  RESULT,
  STATISTIC,
}

enum class DssResult {
  SAFE,
  UNSAFE,
}

/**
 * A message between [DssActor]s, mirroring CPAchecker's five-subtype `DssMessage`. Analysis
 * payloads are optional so stubs like `EchoBlockAnalysis` can omit them.
 */
sealed class DssMessage {

  abstract val senderId: String

  /**
   * Creation order of messages, used by [newDssMessageQueue] to keep equal-priority messages FIFO.
   */
  val sequenceNumber: Long = sequence.getAndIncrement()

  val type: DssMessageType
    get() =
      when (this) {
        is DssPostConditionMessage -> DssMessageType.POST_CONDITION
        is DssViolationConditionMessage -> DssMessageType.VIOLATION_CONDITION
        is DssExceptionMessage -> DssMessageType.EXCEPTION
        is DssResultMessage -> DssMessageType.RESULT
        is DssStatisticsMessage -> DssMessageType.STATISTIC
      }
}

/**
 * A postcondition (CPAchecker's `DssPostConditionMessage`): the disjunction of [postconditions] at
 * the sender's exit, its [precision], and [nonTrivialForEachPredecessor] for the SCC handling.
 */
data class DssPostConditionMessage(
  override val senderId: String,
  val postconditions: List<Expr<BoolType>> = emptyList(),
  val precision: Set<Expr<BoolType>> = emptySet(),
  val nonTrivialForEachPredecessor: Boolean = false,
) : DssMessage() {

  constructor(
    senderId: String,
    postcondition: Expr<BoolType>,
  ) : this(senderId, listOf(postcondition))

  /** The disjunction of [postconditions], or `null` for a bare (stub) message. */
  val postcondition: Expr<BoolType>?
    get() =
      when (postconditions.size) {
        0 -> null
        1 -> postconditions.single()
        else -> Or(postconditions)
      }
}

/**
 * A violation condition (CPAchecker's `DssViolationConditionMessage`): one possibly disjunctive
 * formula at the sender's block entry from which a violation is reachable (see `DssAuxVars`).
 */
data class DssViolationConditionMessage(
  override val senderId: String,
  val violationCondition: Expr<BoolType>? = null,
) : DssMessage()

data class DssExceptionMessage(override val senderId: String, val error: Throwable) : DssMessage()

data class DssResultMessage(override val senderId: String, val result: DssResult) : DssMessage()

data class DssStatisticsMessage(
  override val senderId: String,
  val stats: Map<String, String> = emptyMap(),
) : DssMessage()
