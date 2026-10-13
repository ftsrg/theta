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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToNeutralBvLitExpr
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.model.AtomicFenceLabel.Companion.ATOMIC_MUTEX
import hu.bme.mit.theta.xcfa.model.MutexType.RECURSIVE
import java.math.BigInteger
import java.util.LinkedList
import kotlin.random.Random
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test

class MutexStateTest {
  private val global = ExplState.top()
  private val address = Int(10)
  private val attr = Int(20)
  private val lock = SimpleMutexLock(address)
  private val ret = Var("ret", Int())

  private fun MutexState.call(name: String, vararg params: Expr<*>) =
    apply(
      InvokeLabel(name, listOf(ret.ref) + params, EmptyMetaData, isLibraryFunction = true),
      global,
    )

  private fun recursive() =
    MutexState()
      .call("pthread_mutexattr_init", attr)
      .call("pthread_mutexattr_settype", attr, Int(1))
      .call("pthread_mutex_init", address, attr)

  @Test
  fun recursiveLockIsHeldUntilLastUnlock() {
    val initial = recursive()
    val once = initial.enter(MutexLockLabel(address), 0, global)!!
    val twice = once.enter(MutexLockLabel(address), 0, global)!!
    assertEquals(mapOf(0 to 2), twice.mutexes[lock])
    assertNull(twice.enter(MutexLockLabel(address), 1, global))
    val partial = twice.exit(MutexUnlockLabel(address), 0, global)
    assertEquals(mapOf(0 to 1), partial.mutexes[lock])
    assertNull(partial.enter(MutexLockLabel(address), 1, global))
    val released = partial.exit(MutexUnlockLabel(address), 0, global)
    assertNotNull(released.enter(MutexLockLabel(address), 1, global))
    assertTrue(initial.mutexes.isEmpty())
    assertEquals(mapOf(0 to 1), once.mutexes[lock])
  }

  @Test
  fun normalMutexBlocksItsOwnerAndOtherThreads() {
    val once = MutexState().enter(MutexLockLabel(address), 0, global)!!
    assertNull(once.enter(MutexLockLabel(address), 0, global))
    assertNull(once.enter(MutexTryLockLabel(address, ret), 0, global))
    assertNull(once.enter(MutexLockLabel(address), 1, global))
    assertEquals(once, once.exit(MutexUnlockLabel(address), 1, global))
  }

  @Test
  fun initializationCopiesAttributesAndNullRestoresNormalType() {
    val initial = recursive()
    val changed = initial.call("pthread_mutexattr_settype", attr, Int(0))
    val destroyed = changed.call("pthread_mutexattr_destroy", attr)
    assertEquals(RECURSIVE, destroyed.mutexAttributes[address]?.type)
    assertFalse(attr in destroyed.mutexAttributes)
    val normal = destroyed.call("pthread_mutex_init", address, Int(0))
    assertEquals(MutexAttribute(), normal.mutexAttributes[address])
    val once = normal.enter(MutexLockLabel(address), 0, global)!!
    assertNull(once.enter(MutexLockLabel(address), 0, global))
    assertEquals(MutexAttribute(), changed.mutexAttributes[attr])
    assertEquals(RECURSIVE, initial.mutexAttributes[attr]?.type)
  }

  @Test
  fun readLocksAreCountedPerThreadAndBlockWriters() {
    val read = ReadWriteMutexLock(address, ReadWriteMutexLock.ReadWriteMutexLockType.READ)
    val state =
      MutexState()
        .enter(RWLockReadLockLabel(address), 0, global)!!
        .enter(RWLockReadLockLabel(address), 0, global)!!
        .enter(RWLockReadLockLabel(address), 1, global)!!
    assertEquals(mapOf(0 to 2, 1 to 1), state.mutexes[read])
    assertNull(state.enter(RWLockWriteLockLabel(address), 0, global))
    val partial = state.exit(RWLockUnlockLabel(address), 0, global)
    assertEquals(mapOf(0 to 1, 1 to 1), partial.mutexes[read])
    val other = partial.exit(RWLockUnlockLabel(address), 0, global)
    assertEquals(mapOf(1 to 1), other.mutexes[read])
    assertNull(other.enter(RWLockWriteLockLabel(address), 0, global))
    val released = other.exit(RWLockUnlockLabel(address), 1, global)
    val writer = released.enter(RWLockWriteLockLabel(address), 0, global)!!
    assertNull(writer.enter(RWLockReadLockLabel(address), 0, global))
    assertNull(writer.enter(RWLockWriteLockLabel(address), 1, global))
  }

  @Test
  fun atomicBlocksKeepTheirExistingNestingSemantics() {
    val nested =
      MutexState().enter(AtomicBeginLabel(), 0, global)!!.enter(AtomicBeginLabel(), 0, global)!!
    assertEquals(mapOf(0 to 1), nested.mutexes[ATOMIC_MUTEX])
    assertNull(nested.enter(AtomicBeginLabel(), 1, global))
    assertTrue(nested.exit(AtomicEndLabel(), 0, global).mutexes.isEmpty())
  }

  @Test
  fun unknownAddressesAndTypesAreRejected() {
    val unknown = Var("unknown", Int()).ref
    assertThrows(IllegalStateException::class.java) {
      MutexState().call("pthread_mutexattr_settype", unknown, Int(1))
    }
    assertThrows(IllegalStateException::class.java) {
      MutexState().call("pthread_mutex_init", unknown, Int(0))
    }
    assertThrows(IllegalStateException::class.java) {
      MutexState().call("pthread_mutex_init", address, unknown)
    }
    assertThrows(IllegalStateException::class.java) {
      MutexState().call("pthread_mutexattr_settype", attr, unknown)
    }
    assertThrows(IllegalStateException::class.java) {
      MutexState().call("pthread_mutexattr_settype", attr, Int(2))
    }
    assertThrows(IllegalStateException::class.java) {
      MutexState().exit(MutexUnlockLabel(unknown), 0, global)
    }
  }

  @Test
  fun bitvectorMutexTypesAndNullAttributesAreSupported() {
    val recursive =
      MutexState()
        .call("pthread_mutexattr_init", attr)
        .call("pthread_mutexattr_settype", attr, bigIntegerToNeutralBvLitExpr(BigInteger.ONE, 32))
        .call("pthread_mutex_init", address, attr)
    assertEquals(RECURSIVE, recursive.mutexAttributes[address]?.type)
    val normal =
      recursive.call(
        "pthread_mutex_init",
        address,
        bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 64),
      )
    assertEquals(MutexAttribute(), normal.mutexAttributes[address])
  }

  @Test
  fun addressesAreResolvedFromWrappedExplicitStates() {
    val pointer = Var("pointer", Int())
    val explicit = ExplState.of(ImmutableValuation.builder().put(pointer, attr).build())
    val label =
      InvokeLabel(
        "pthread_mutexattr_init",
        listOf(ret.ref, pointer.ref),
        EmptyMetaData,
        isLibraryFunction = true,
      )
    val initialized = MutexState().apply(label, PtrState(explicit))
    assertEquals(MutexAttribute(), initialized.mutexAttributes[attr])
  }

  @Test
  fun unrelatedLibraryCallsLeaveMutexStateUnchanged() {
    val mutexState = recursive()
    val label =
      InvokeLabel("unknown_library_function", emptyList(), EmptyMetaData, isLibraryFunction = true)
    assertSame(mutexState, mutexState.apply(label, global))
    val initial = state(mutexState)
    val loc = initial.processes.getValue(0).locs.peek()
    loc.outgoingEdges.add(XcfaEdge(loc, loc, label, EmptyMetaData))
    val action = getXcfaLts(Random(0)).getEnabledActionsFor(initial).single()
    val result = initial.apply(action)
    assertEquals(initial.processes, result.processes)
    assertEquals(mutexState, result.mutexState)
  }

  private fun state(mutexState: MutexState): XcfaState<PtrState<ExplState>> {
    val loc = XcfaLocation("loc", metadata = EmptyMetaData)
    return XcfaState(
      null,
      mapOf(
        0 to
          XcfaProcessState(
            LinkedList(listOf(loc)),
            LinkedList(listOf(emptyMap())),
            paramsInitialized = true,
          )
      ),
      PtrState(global),
      mutexState,
    )
  }

  @Test
  fun ltsHandlesLibraryCallsAndRecursiveTryLockBranches() {
    val initial = state(MutexState())
    val loc = initial.processes.getValue(0).locs.peek()
    val init =
      InvokeLabel(
        "pthread_mutex_init",
        listOf(ret.ref, address, Int(0)),
        EmptyMetaData,
        isLibraryFunction = true,
      )
    val initEdge = XcfaEdge(loc, loc, init, EmptyMetaData)
    loc.outgoingEdges.add(initEdge)
    val initialized = initial.apply(getXcfaLts(Random(0)).getEnabledActionsFor(initial).single())
    loc.outgoingEdges.clear()
    assertEquals(MutexAttribute(), initialized.mutexState.mutexAttributes[address])
    val recursive = initialized.copy(mutexState = recursive())
    val locked =
      recursive.apply(XcfaAction(0, XcfaEdge(loc, loc, MutexLockLabel(address), EmptyMetaData)))
    val edge =
      XcfaEdge(
        loc,
        XcfaLocation("target", metadata = EmptyMetaData),
        MutexTryLockLabel(address, ret),
        EmptyMetaData,
      )
    loc.outgoingEdges.add(edge)
    val enabled = getXcfaLts(Random(0)).getEnabledActionsFor(locked)
    assertEquals(1, enabled.size)
    val result = locked.apply(enabled.single())
    assertEquals(mapOf(0 to 2), result.mutexes[lock])
    val normal = locked.copy(mutexState = MutexState(locked.mutexes))
    val failed = getXcfaLts(Random(0)).getEnabledActionsFor(normal)
    assertEquals(1, failed.size)
    assertEquals(normal.mutexes, normal.apply(failed.single()).mutexes)
  }

  @Test
  fun coverageDistinguishesAttributesAndLockCounts() {
    val initial = state(recursive())
    val once =
      initial.copy(mutexState = initial.mutexState.enter(MutexLockLabel(address), 0, global)!!)
    val twice = once.copy(mutexState = once.mutexState.enter(MutexLockLabel(address), 0, global)!!)
    val normal = initial.copy(mutexState = MutexState())
    val core = PartialOrd<PtrState<ExplState>> { _, _ -> true }
    listOf(getPartialOrder(core), getStackPartialOrder(core)).forEach { order ->
      assertFalse(order.isLeq(once, twice))
      assertFalse(order.isLeq(twice, once))
      assertFalse(order.isLeq(initial, normal))
      assertFalse(order.isLeq(normal, initial))
      assertTrue(order.isLeq(once, once))
    }
  }
}
