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
import java.util.Objects

/**
 * The wrapped relation intersected with a structural upper bound of it (an extracted bound MDD, see
 * `extractBound`). Keys the bound knows absent are pruned without consulting the wrapped
 * (procedural) relation, and where the bound has no default edge its keys are exhaustive: target
 * enumeration is driven by bounded point queries instead of open solver enumeration. The bound
 * overapproximates the relation, so pruning is semantically the identity — only the effort changes.
 * The new-literal levels on top have no counterpart in a bound extracted earlier; consultation
 * starts where the level's trace info matches the bound's top, and bounds are level-dense below
 * their top, consuming one level per step from there.
 */
class NegativeNextStateDescriptor
private constructor(
  private val wrapped: AbstractNextStateDescriptor,
  private val bound: MddHandle,
) : AbstractNextStateDescriptor {

  companion object {
    @JvmStatic
    fun of(wrapped: AbstractNextStateDescriptor, bound: MddHandle?): AbstractNextStateDescriptor =
      when {
        wrapped == AbstractNextStateDescriptor.terminalEmpty() -> wrapped
        bound == null || bound.isTerminal && !bound.isTerminalZero -> wrapped
        bound.isTerminalZero -> AbstractNextStateDescriptor.terminalEmpty()
        else -> NegativeNextStateDescriptor(wrapped, bound)
      }

    @JvmStatic
    fun of(
      wrapped: AbstractNextStateDescriptor.Postcondition,
      bound: MddHandle?,
    ): AbstractNextStateDescriptor.Postcondition =
      when {
        wrapped == AbstractNextStateDescriptor.Postcondition.terminalEmpty() -> wrapped
        bound == null || bound.isTerminal && !bound.isTerminalZero -> wrapped
        bound.isTerminalZero -> AbstractNextStateDescriptor.Postcondition.terminalEmpty()
        else -> Postcondition(wrapped, bound)
      }

    /** The bound's child for [key]; null = known absent. Missing keys fall back to the default. */
    internal fun childOf(bound: MddHandle, key: Int): MddHandle? {
      val node = bound.node.get(key) ?: bound.node.defaultValue() ?: return null
      if (node == bound.variableHandle.mddGraph.terminalZeroNode) return null
      return bound.variableHandle.lower.orElseThrow().getHandleFor(node)
    }

    /** The bound's full edge set when exhaustive (no default edge), else null. */
    internal fun boundedKeys(bound: MddHandle): IntSetView? =
      if (bound.node.defaultValue() == null) bound.node.keySet() else null

    private fun aligned(localStateSpace: StateSpaceInfo, bound: MddHandle): Boolean =
      localStateSpace.traceInfo == bound.variableHandle.variable.orElseThrow().traceInfo
  }

  override fun getDiagonal(
    localStateSpace: StateSpaceInfo
  ): IntObjMapView<AbstractNextStateDescriptor> {
    val diagonal = wrapped.getDiagonal(localStateSpace)
    if (!aligned(localStateSpace, bound)) {
      return IntObjMapViews.Transforming(diagonal) { d, _ -> of(d, bound) }
    }
    return IntObjMapViews.Transforming(diagonal) { d, key ->
      if (d == null || key == null) AbstractNextStateDescriptor.terminalEmpty()
      else {
        val from = childOf(bound, key)
        if (from == null) AbstractNextStateDescriptor.terminalEmpty()
        else if (from.isTerminal) d
        else {
          val to = childOf(from, key)
          if (to == null) AbstractNextStateDescriptor.terminalEmpty() else of(d, to)
        }
      }
    }
  }

  override fun getOffDiagonal(
    localStateSpace: StateSpaceInfo
  ): IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> {
    val offDiagonal = wrapped.getOffDiagonal(localStateSpace)
    if (!aligned(localStateSpace, bound)) {
      return IntObjMapViews.Transforming(offDiagonal) { inner ->
        IntObjMapViews.Transforming(inner) { d, _ -> of(d, bound) }
      }
    }
    return IntObjMapViews.Transforming(offDiagonal) { inner, from ->
      if (inner == null || from == null)
        IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty())
      else {
        val boundFrom = childOf(bound, from)
        if (boundFrom == null) IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty())
        else constrainInner(inner, boundFrom)
      }
    }
  }

  private fun constrainInner(
    inner: IntObjMapView<AbstractNextStateDescriptor>,
    boundTo: MddHandle,
  ): IntObjMapView<AbstractNextStateDescriptor> {
    if (boundTo.isTerminal) return inner
    return object : IntObjMapView<AbstractNextStateDescriptor> {
      override fun cursor(): IntObjCursor<out AbstractNextStateDescriptor> {
        val bounded = boundedKeys(boundTo)
        return if (bounded != null) boundDrivenCursor(bounded) else filteredCursor()
      }

      // the bound's edge set is exhaustive: probe the relation by key instead of open solver
      // enumeration
      private fun boundDrivenCursor(keys: IntSetView): IntObjCursor<AbstractNextStateDescriptor> {
        val c = keys.cursor()
        return object : IntObjCursor<AbstractNextStateDescriptor> {
          private var value: AbstractNextStateDescriptor =
            AbstractNextStateDescriptor.terminalEmpty()

          override fun key() = c.elem()

          override fun value() = value

          override fun moveNext(): Boolean {
            while (c.moveNext()) {
              val target = inner.get(c.elem()) ?: continue
              val and = of(target, childOf(boundTo, c.elem()))
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

          override fun value() = of(c.value(), childOf(boundTo, c.key()))

          override fun moveNext(): Boolean {
            while (c.moveNext()) {
              if (childOf(boundTo, c.key()) != null) return true
            }
            return false
          }
        }
      }

      override fun get(key: Int): AbstractNextStateDescriptor {
        val child = childOf(boundTo, key) ?: return AbstractNextStateDescriptor.terminalEmpty()
        return of(inner.get(key), child)
      }

      override fun isEmpty() = throw UnsupportedOperationException()

      override fun isProcedural() = throw UnsupportedOperationException()

      override fun containsKey(key: Int) = throw UnsupportedOperationException()

      override fun defaultValue() = throw UnsupportedOperationException()

      override fun size() = throw UnsupportedOperationException()
    }
  }

  override fun split(): java.util.Optional<Iterable<AbstractNextStateDescriptor>> =
    wrapped.split().map { iterable -> iterable.map { of(it, bound) } }

  override fun isLocallyIdentity(stateSpaceInfo: StateSpaceInfo): Boolean =
    wrapped.isLocallyIdentity(stateSpaceInfo)

  override fun evaluate(): Boolean = wrapped.evaluate()

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is NegativeNextStateDescriptor) return false
    return wrapped == other.wrapped && bound == other.bound
  }

  override fun hashCode(): Int = Objects.hash(wrapped, bound)

  override fun toString(): String = "AndByBound($wrapped, $bound)"

  private class Postcondition(
    private val wrapped: AbstractNextStateDescriptor.Postcondition,
    private val bound: MddHandle,
  ) : AbstractNextStateDescriptor.Postcondition {

    override fun getValuations(
      localStateSpace: StateSpaceInfo
    ): IntObjMapView<AbstractNextStateDescriptor> {
      val valuations = wrapped.getValuations(localStateSpace)
      if (!aligned(localStateSpace, bound)) {
        return IntObjMapViews.Transforming(valuations) { d, _ -> wrap(d, bound) }
      }
      return object : IntObjMapView<AbstractNextStateDescriptor> {
        override fun cursor(): IntObjCursor<out AbstractNextStateDescriptor> {
          val bounded = boundedKeys(bound)
          return if (bounded != null) boundDrivenCursor(bounded) else filteredCursor()
        }

        private fun boundDrivenCursor(keys: IntSetView): IntObjCursor<AbstractNextStateDescriptor> {
          val c = keys.cursor()
          return object : IntObjCursor<AbstractNextStateDescriptor> {
            private var value: AbstractNextStateDescriptor =
              AbstractNextStateDescriptor.terminalEmpty()

            override fun key() = c.elem()

            override fun value() = value

            override fun moveNext(): Boolean {
              while (c.moveNext()) {
                val target = valuations.get(c.elem()) ?: continue
                val and = wrap(target, childOf(bound, c.elem()))
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

            override fun value() = wrap(c.value(), childOf(bound, c.key()))

            override fun moveNext(): Boolean {
              while (c.moveNext()) {
                if (childOf(bound, c.key()) != null) return true
              }
              return false
            }
          }
        }

        override fun get(key: Int): AbstractNextStateDescriptor {
          val child = childOf(bound, key) ?: return AbstractNextStateDescriptor.terminalEmpty()
          return wrap(valuations.get(key), child)
        }

        // the initializer relational product canonizes a template over this view, which needs
        // the metadata of the wrapped view; with bounded keys the view is effectively explicit
        // (statistics iterate the bounded cursor instead of draining an open enumeration)
        override fun isEmpty() = valuations.isEmpty()

        override fun isProcedural() = boundedKeys(bound) == null && valuations.isProcedural()

        override fun containsKey(key: Int) =
          childOf(bound, key) != null && valuations.containsKey(key)

        override fun defaultValue(): AbstractNextStateDescriptor? = valuations.defaultValue()

        override fun size(): Int {
          if (boundedKeys(bound) == null) return valuations.size()
          var n = 0
          val c = cursor()
          while (c.moveNext()) n++
          return n
        }
      }
    }

    /**
     * The relProd initializer patch dispatches on Postcondition, so children stay Postconditions.
     */
    private fun wrap(
      d: AbstractNextStateDescriptor?,
      bound: MddHandle?,
    ): AbstractNextStateDescriptor =
      when (d) {
        null -> AbstractNextStateDescriptor.terminalEmpty()
        is AbstractNextStateDescriptor.Postcondition -> of(d, bound)
        else -> of(d, bound)
      }

    override fun evaluate(): Boolean = wrapped.evaluate()

    override fun equals(other: Any?): Boolean {
      if (this === other) return true
      if (other !is Postcondition) return false
      return wrapped == other.wrapped && bound == other.bound
    }

    override fun hashCode(): Int = Objects.hash(wrapped, bound)

    override fun toString(): String = "AndByBound($wrapped, $bound)"
  }
}
