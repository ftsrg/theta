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
 * A message exchanged between [DssActor]s. Mirrors CPAchecker's `DssMessage` hierarchy, which has
 * five subtypes (the paper only describes the two analysis messages, `post` and `vcond`).
 *
 * The analysis payloads are optional so the stub behaviors this runtime was validated against
 * (`EchoBlockAnalysis`) can send bare messages; [PredicateBlockBehavior] always fills them in.
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
 * A postcondition, CPAchecker's `DssPostConditionMessage`. Like CPAchecker, one message can carry
 * several abstract states ([postconditions], each a formula over the program variables at the
 * sender's block exit; their disjunction is the postcondition), the precision the sender used
 * ([precision], CPAchecker serializes the `PredicatePrecision` with every state), and whether the
 * states were computed while the sender had a non-trivial precondition from each of its own
 * predecessors ([nonTrivialForEachPredecessor], CPAchecker's
 * `BlockState.hasNonTrivialSummaryForEachPredecessor`, used for the strongly-connected-component
 * handling of the paper).
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
 * A violation condition, CPAchecker's `DssViolationConditionMessage`: a formula over the program
 * variables at the entry of the sender's block (plus existentially quantified auxiliary variables,
 * see `DssAuxVars`) from which a specification violation is reachable. CPAchecker combines the
 * conditions of one block at the same program location into one state (`combineVcsByHash`), so a
 * message carries a single, possibly disjunctive, condition.
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
