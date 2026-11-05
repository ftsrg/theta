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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import java.util.concurrent.atomic.AtomicLong

private val sequence = AtomicLong()

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

/** CPAchecker's `DssMessage`. */
sealed class DssMessage {

  abstract val senderId: String

  /** Keeps equal-priority messages FIFO in [createDssMessageQueue]. */
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

data class DssPostConditionMessage(
  override val senderId: String,
  val postconditions: List<Expr<BoolType>> = emptyList(),
  val precision: Set<Expr<BoolType>> = emptySet(),
) : DssMessage() {

  constructor(
    senderId: String,
    postcondition: Expr<BoolType>,
  ) : this(senderId, listOf(postcondition))

  val postcondition: Expr<BoolType>?
    get() = postconditions.takeIf { it.isNotEmpty() }?.let { Or(it) }
}

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
