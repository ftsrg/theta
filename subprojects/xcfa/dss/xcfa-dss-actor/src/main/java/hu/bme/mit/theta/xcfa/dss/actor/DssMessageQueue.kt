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

import java.util.concurrent.BlockingQueue
import java.util.concurrent.PriorityBlockingQueue

/** CPAchecker's `DssDefaultQueue`: `RESULT`/`EXCEPTION`/`STATISTIC` first, else FIFO. */
fun createDssMessageQueue(): BlockingQueue<DssMessage> =
  PriorityBlockingQueue(11, compareBy<DssMessage>({ it.priority }, { it.sequenceNumber }))

private val DssMessage.priority: Int
  get() =
    when (type) {
      DssMessageType.RESULT,
      DssMessageType.EXCEPTION,
      DssMessageType.STATISTIC -> 0
      DssMessageType.POST_CONDITION,
      DssMessageType.VIOLATION_CONDITION -> 1
    }
