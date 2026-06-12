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
package hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode

import hu.bme.mit.delta.collections.IntObjMapView
import hu.bme.mit.delta.collections.RecursiveIntObjCursor
import hu.bme.mit.delta.collections.RecursiveIntObjMapView
import hu.bme.mit.delta.java.mdd.MddNode
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation

/**
 * The lower bound of an explored node: the edges exploration has already established, as the node's
 * own map view interface, so consumers need no instanceof dispatch on the representation. Answers
 * purely from the caches, never calling solvers. Recursion through [cursor] stays inside known
 * edges too. Identity nodes carry no enumerable edges and appear empty; their level-pair structure
 * remains the caller's concern.
 */
class MddPresentView private constructor(private val known: IntObjMapView<MddNode>) :
  RecursiveIntObjMapView<MddNode> {

  companion object {
    @JvmStatic
    fun of(node: MddNode): MddPresentView =
      when {
        node.isTerminal -> MddPresentView(IntObjMapView.empty())
        node.representation is MddExpressionRepresentation ->
          MddPresentView(
            (node.representation as MddExpressionRepresentation).explicitRepresentation.cacheView
          )
        node.representation is IdentityRepresentation -> MddPresentView(IntObjMapView.empty())
        // structural nodes are explicit already
        else -> MddPresentView(node)
      }
  }

  override fun isEmpty(): Boolean = known.isEmpty

  override fun isProcedural(): Boolean = false

  override fun containsKey(key: Int): Boolean = known.containsKey(key)

  override fun get(key: Int): MddNode? = known.get(key)

  override fun defaultValue(): MddNode? = known.defaultValue()

  override fun size(): Int = known.size()

  override fun cursor(): RecursiveIntObjCursor<out MddNode> = Cursor(known)

  private class Cursor(private val known: IntObjMapView<MddNode>) : RecursiveIntObjCursor<MddNode> {

    private val flat = known.cursor()
    private var key = 0
    private var value: MddNode? = null

    override fun moveNext(): Boolean {
      val moved = flat.moveNext()
      key = if (moved) flat.key() else 0
      value = if (moved) flat.value() else null
      return moved
    }

    override fun moveTo(key: Int): Boolean {
      val found = known.get(key) ?: return false
      this.key = key
      this.value = found
      return true
    }

    override fun key(): Int {
      check(value != null) { "Cursor is not positioned" }
      return key
    }

    override fun value(): MddNode = checkNotNull(value) { "Cursor is not positioned" }

    override fun valueCursor(): RecursiveIntObjCursor<out MddNode> = of(value()).cursor()

    override fun close() {}
  }
}
