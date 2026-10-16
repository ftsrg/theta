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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.analysis.MutexState
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.params.Domain
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.model.ReadWriteMutexLock.ReadWriteMutexLockType.READ
import hu.bme.mit.theta.xcfa.model.ReadWriteMutexLock.ReadWriteMutexLockType.WRITE
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class MutexStateSerializationTest {
  @Test
  fun roundTripPreservesLibraryCallDispatch() {
    val label =
      InvokeLabel(
        "pthread_mutexattr_settype",
        listOf(Int(0), Int(20), Int(1)),
        EmptyMetaData,
        isLibraryFunction = true,
      )
    val gson = getGson(domain = { Domain.EXPL })
    val restored = gson.fromJson(gson.toJson(label, XcfaLabel::class.java), XcfaLabel::class.java)
    assertEquals(label, restored)
  }

  @Test
  fun roundTripPreservesAttributesCountsAndLockKinds() {
    val mutexState =
      MutexState(
        mapOf(
          SimpleMutexLock(Int(10)) to mapOf(0 to 2),
          ReadWriteMutexLock(Int(11), READ) to mapOf(0 to 2, 1 to 1),
          ReadWriteMutexLock(Int(12), WRITE) to mapOf(2 to 1),
        ),
        mapOf(Int(10) to MutexAttribute(MutexType.RECURSIVE), Int(20) to MutexAttribute()),
      )
    val state = XcfaState(null, emptyMap(), ExplState.top(), mutexState)
    val gson = getGson(domain = { Domain.EXPL })
    val restored = gson.fromJson(gson.toJson(state), XcfaState::class.java)
    assertEquals(mutexState, restored.mutexState)
  }
}
