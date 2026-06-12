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
package hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl

import hu.bme.mit.delta.collections.IntObjCursor
import hu.bme.mit.delta.collections.IntObjMapView
import hu.bme.mit.delta.collections.IntSetView
import hu.bme.mit.delta.collections.impl.IntObjMapViews
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation
import java.util.Objects

/**
 * Prunes a wrapped relation by the previous iteration's node, consulting only its cached knowledge
 * (explicit children, negative cache, completeness) — never the solver. Refinement only conjoins
 * constraints, so the new relation is a subset of the old one: branches the old node is known to
 * lack are dropped, and where the old node is complete, target enumeration is driven by its
 * explicit keys, replacing open solver enumeration of the new node with bounded point queries.
 * Unknown knowledge falls back to the wrapped behavior. The new-literal levels on top have no old
 * counterpart; consultation starts where the level's trace info matches the old node's top.
 */
class NegativeNextStateDescriptor
private constructor(
  private val wrapped: AbstractNextStateDescriptor,
  private val prev: MddHandle,
) : AbstractNextStateDescriptor {

  companion object {
    @JvmStatic
    fun of(wrapped: AbstractNextStateDescriptor, prev: MddHandle?): AbstractNextStateDescriptor =
      when {
        wrapped == AbstractNextStateDescriptor.terminalEmpty() -> wrapped
        prev == null || prev.isTerminal && !prev.isTerminalZero -> wrapped
        prev.isTerminalZero -> AbstractNextStateDescriptor.terminalEmpty()
        else -> NegativeNextStateDescriptor(wrapped, prev)
      }

    @JvmStatic
    fun of(
      wrapped: AbstractNextStateDescriptor.Postcondition,
      prev: MddHandle?,
    ): AbstractNextStateDescriptor.Postcondition =
      when {
        wrapped == AbstractNextStateDescriptor.Postcondition.terminalEmpty() -> wrapped
        prev == null || prev.isTerminal && !prev.isTerminalZero -> wrapped
        prev.isTerminalZero -> AbstractNextStateDescriptor.Postcondition.terminalEmpty()
        else -> Postcondition(wrapped, prev)
      }

    /** The old node knows the key has no edge. Cached knowledge only, no solver. */
    internal fun knownAbsent(prev: MddHandle, key: Int): Boolean {
      val repr = prev.node.representation
      if (repr !is MddExpressionRepresentation) return false
      val explicit = repr.explicitRepresentation
      if (explicit.cacheView.defaultValue() != null) return false
      return explicit.isNegativelyCached(key) ||
        explicit.isComplete && !explicit.cacheView.containsKey(key)
    }

    /** The old node's cached child for the key, or null if unknown. */
    internal fun knownChild(prev: MddHandle, key: Int): MddHandle? {
      val repr = prev.node.representation
      if (repr !is MddExpressionRepresentation) return null
      val explicit = repr.explicitRepresentation
      val child = explicit.cacheView.defaultValue() ?: explicit.cacheView.get(key) ?: return null
      return prev.variableHandle.lower.orElseThrow().getHandleFor(child)
    }

    /** The old node's full edge set when known (complete, no default), else null. */
    internal fun boundedKeys(prev: MddHandle): IntSetView? {
      val repr = prev.node.representation
      if (repr !is MddExpressionRepresentation) return null
      val explicit = repr.explicitRepresentation
      return if (explicit.isComplete && explicit.cacheView.defaultValue() == null)
        explicit.cacheView.keySet()
      else null
    }

    private fun aligned(localStateSpace: StateSpaceInfo, prev: MddHandle): Boolean =
      localStateSpace.traceInfo == prev.variableHandle.variable.orElseThrow().traceInfo
  }

  override fun getDiagonal(
    localStateSpace: StateSpaceInfo
  ): IntObjMapView<AbstractNextStateDescriptor> {
    val diagonal = wrapped.getDiagonal(localStateSpace)
    if (!aligned(localStateSpace, prev)) {
      return IntObjMapViews.Transforming(diagonal) { d, _ -> of(d, prev) }
    }
    val repr = prev.node.representation
    if (repr is IdentityRepresentation) {
      val cont =
        prev.variableHandle.lower
          .orElseThrow()
          .lower
          .orElseThrow()
          .getHandleFor(repr.continuation)
      return IntObjMapViews.Transforming(diagonal) { d, _ -> of(d, cont) }
    }
    return IntObjMapViews.Transforming(diagonal) { d, key ->
      if (d == null || key == null) AbstractNextStateDescriptor.terminalEmpty()
      else if (knownAbsent(prev, key)) AbstractNextStateDescriptor.terminalEmpty()
      else {
        val oldFrom = knownChild(prev, key)
        if (oldFrom == null) d
        else if (knownAbsent(oldFrom, key)) AbstractNextStateDescriptor.terminalEmpty()
        else of(d, knownChild(oldFrom, key))
      }
    }
  }

  override fun getOffDiagonal(
    localStateSpace: StateSpaceInfo
  ): IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> {
    val offDiagonal = wrapped.getOffDiagonal(localStateSpace)
    if (!aligned(localStateSpace, prev)) {
      return IntObjMapViews.Transforming(offDiagonal) { inner ->
        IntObjMapViews.Transforming(inner) { d, _ -> of(d, prev) }
      }
    }
    val repr = prev.node.representation
    if (repr is IdentityRepresentation) {
      // an identity relation has no off-diagonal edges
      return IntObjMapView.empty(IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty()))
    }
    return IntObjMapViews.Transforming(offDiagonal) { inner, from ->
      if (inner == null || from == null) IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty())
      else if (knownAbsent(prev, from))
        IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty())
      else constrainInner(inner, knownChild(prev, from))
    }
  }

  private fun constrainInner(
    inner: IntObjMapView<AbstractNextStateDescriptor>,
    oldTo: MddHandle?,
  ): IntObjMapView<AbstractNextStateDescriptor> {
    if (oldTo == null || oldTo.isTerminal && !oldTo.isTerminalZero) return inner
    if (oldTo.isTerminalZero) return IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty())
    return object : IntObjMapView<AbstractNextStateDescriptor> {
      override fun cursor(): IntObjCursor<out AbstractNextStateDescriptor> {
        val bounded = boundedKeys(oldTo)
        return if (bounded != null) oldDrivenCursor(bounded) else filteredCursor()
      }

      // the old node's edge set is fully known and bounds the new one: probe the new relation by
      // key instead of open solver enumeration
      private fun oldDrivenCursor(keys: IntSetView): IntObjCursor<AbstractNextStateDescriptor> {
        val c = keys.cursor()
        return object : IntObjCursor<AbstractNextStateDescriptor> {
          private var value: AbstractNextStateDescriptor =
            AbstractNextStateDescriptor.terminalEmpty()

          override fun key() = c.elem()

          override fun value() = value

          override fun moveNext(): Boolean {
            while (c.moveNext()) {
              val target = inner.get(c.elem()) ?: continue
              val and = of(target, knownChild(oldTo, c.elem()))
              if (and != AbstractNextStateDescriptor.terminalEmpty()) {
                value = and
                return true
              }
            }
            return false
          }
        }
      }

      private fun filteredCursor(): IntObjCursor<AbstractNextStateDescriptor> {
        val c = inner.cursor()
        return object : IntObjCursor<AbstractNextStateDescriptor> {
          override fun key() = c.key()

          override fun value() = of(c.value(), knownChild(oldTo, c.key()))

          override fun moveNext(): Boolean {
            while (c.moveNext()) {
              if (!knownAbsent(oldTo, c.key())) return true
            }
            return false
          }
        }
      }

      override fun get(key: Int): AbstractNextStateDescriptor =
        if (knownAbsent(oldTo, key)) AbstractNextStateDescriptor.terminalEmpty()
        else of(inner.get(key), knownChild(oldTo, key))

      override fun isEmpty() = throw UnsupportedOperationException()

      override fun isProcedural() = throw UnsupportedOperationException()

      override fun containsKey(key: Int) = throw UnsupportedOperationException()

      override fun defaultValue() = throw UnsupportedOperationException()

      override fun size() = throw UnsupportedOperationException()
    }
  }

  override fun split(): java.util.Optional<Iterable<AbstractNextStateDescriptor>> =
    wrapped.split().map { iterable -> iterable.map { of(it, prev) } }

  override fun isLocallyIdentity(stateSpaceInfo: StateSpaceInfo): Boolean =
    wrapped.isLocallyIdentity(stateSpaceInfo)

  override fun evaluate(): Boolean = wrapped.evaluate()

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is NegativeNextStateDescriptor) return false
    return wrapped == other.wrapped && prev == other.prev
  }

  override fun hashCode(): Int = Objects.hash(wrapped, prev)

  override fun toString(): String = "AndByPrev($wrapped, $prev)"

  private class Postcondition(
    private val wrapped: AbstractNextStateDescriptor.Postcondition,
    private val prev: MddHandle,
  ) : AbstractNextStateDescriptor.Postcondition {

    override fun getValuations(
      localStateSpace: StateSpaceInfo
    ): IntObjMapView<AbstractNextStateDescriptor> {
      val valuations = wrapped.getValuations(localStateSpace)
      if (!aligned(localStateSpace, prev)) {
        return IntObjMapViews.Transforming(valuations) { d, _ -> wrap(d, prev) }
      }
      return object : IntObjMapView<AbstractNextStateDescriptor> {
        override fun cursor(): IntObjCursor<out AbstractNextStateDescriptor> {
          val bounded = boundedKeys(prev)
          return if (bounded != null) oldDrivenCursor(bounded) else filteredCursor()
        }

        private fun oldDrivenCursor(keys: IntSetView): IntObjCursor<AbstractNextStateDescriptor> {
          val c = keys.cursor()
          return object : IntObjCursor<AbstractNextStateDescriptor> {
            private var value: AbstractNextStateDescriptor =
              AbstractNextStateDescriptor.terminalEmpty()

            override fun key() = c.elem()

            override fun value() = value

            override fun moveNext(): Boolean {
              while (c.moveNext()) {
                val target = valuations.get(c.elem()) ?: continue
                val and = wrap(target, knownChild(prev, c.elem()))
                if (and != AbstractNextStateDescriptor.terminalEmpty()) {
                  value = and
                  return true
                }
              }
              return false
            }
          }
        }

        private fun filteredCursor(): IntObjCursor<AbstractNextStateDescriptor> {
          val c = valuations.cursor()
          return object : IntObjCursor<AbstractNextStateDescriptor> {
            override fun key() = c.key()

            override fun value() = wrap(c.value(), knownChild(prev, c.key()))

            override fun moveNext(): Boolean {
              while (c.moveNext()) {
                if (!knownAbsent(prev, c.key())) return true
              }
              return false
            }
          }
        }

        override fun get(key: Int): AbstractNextStateDescriptor =
          if (knownAbsent(prev, key)) AbstractNextStateDescriptor.terminalEmpty()
          else wrap(valuations.get(key), knownChild(prev, key))

        // the initializer relational product canonizes a template over this view, which needs
        // the metadata of the wrapped view; with bounded keys the view is effectively explicit
        // (statistics iterate the bounded cursor instead of draining an open enumeration)
        override fun isEmpty() = valuations.isEmpty()

        override fun isProcedural() = boundedKeys(prev) == null && valuations.isProcedural()

        override fun containsKey(key: Int) =
          !knownAbsent(prev, key) && valuations.containsKey(key)

        override fun defaultValue(): AbstractNextStateDescriptor? = valuations.defaultValue()

        override fun size(): Int {
          if (boundedKeys(prev) == null) return valuations.size()
          var n = 0
          val c = cursor()
          while (c.moveNext()) n++
          return n
        }
      }
    }

    /** The relProd initializer patch dispatches on Postcondition, so children stay Postconditions. */
    private fun wrap(d: AbstractNextStateDescriptor?, old: MddHandle?): AbstractNextStateDescriptor =
      when (d) {
        null -> AbstractNextStateDescriptor.terminalEmpty()
        is AbstractNextStateDescriptor.Postcondition -> of(d, old)
        else -> of(d, old)
      }

    override fun evaluate(): Boolean = wrapped.evaluate()

    override fun equals(other: Any?): Boolean {
      if (this === other) return true
      if (other !is Postcondition) return false
      return wrapped == other.wrapped && prev == other.prev
    }

    override fun hashCode(): Int = Objects.hash(wrapped, prev)

    override fun toString(): String = "AndByPrev($wrapped, $prev)"
  }
}
