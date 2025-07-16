/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.frontend.models

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr

interface Btor2NodeVisitor<R, P> {
  fun visit(node: Btor2UnaryOperation, param: P): R

  fun visit(node: Btor2BinaryOperation, param: P): R

  fun visit(node: Btor2TernaryOperation, param: P): R

  fun visit(node: Btor2SliceOperation, param: P): R

  fun visit(node: Btor2ExtOperation, param: P): R

  fun visit(node: Btor2Comparison, param: P): R

  fun visit(node: Btor2Boolean, param: P): R

  fun visit(node: Btor2BitvecSort, param: P): R

  fun visit(node: Btor2Input, param: P): R

  fun visit(node: Btor2State, param: P): R

  fun visit(node: Btor2Init, param: P): R

  fun visit(node: Btor2Next, param: P): R

  fun visit(node: Btor2Bad, param: P): R

  fun visit(node: Btor2Const, param: P): R
}

object Btor2Circuit {
  private val _nodes = mutableMapOf<UInt, Btor2Node>()
  private val _sorts = mutableMapOf<UInt, Btor2Sort>()
  private val _constants = mutableMapOf<UInt, Btor2Const>()
  private val _ops = mutableMapOf<UInt, Btor2Operation>()
  private val _states = mutableMapOf<UInt, Btor2Stateful>()
  private val _properties = mutableMapOf<UInt, Btor2Bad>()

  val nodes: Map<UInt, Btor2Node>
    get() = _nodes

  val sorts: Map<UInt, Btor2Sort>
    get() = _sorts

  val constants: Map<UInt, Btor2Const>
    get() = _constants

  val ops: Map<UInt, Btor2Operation>
    get() = _ops

  val states: Map<UInt, Btor2Stateful>
    get() = _states

  val properties: Map<UInt, Btor2Bad>
    get() = _properties

  fun addSort(sort: Btor2Sort) {
    _sorts[sort.sid] = sort
  }

  fun addNode(node: Btor2Node) {
    _nodes[node.nid] = node
    when (node) {
      is Btor2Const -> _constants[node.nid] = node
      is Btor2Operation -> _ops[node.nid] = node
      is Btor2Stateful -> _states[node.nid] = node
      is Btor2Bad -> _properties[node.nid] = node
      else -> error("Btor2Circuit cannot sort this type: ${node.javaClass}")
    }
  }
}

// sortID lookup in Btor2Sort
abstract class Btor2Node(id: UInt, btor2Sort: Btor2Sort? = null) {
  abstract val nid: UInt
  abstract val sort: Btor2Sort?

  open fun getVar(): VarDecl<*>? {
    return null
  }

  abstract fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param: P): R

  abstract fun getExpr(): Expr<*>
}

abstract class Btor2Sort(sid: UInt, width: UInt) {
  abstract val sid: UInt
  abstract val width: UInt
}

// Ezt egyelőre nem használjuk mert csak bitvektoraink vannak
data class Btor2BitvecSort(override val sid: UInt, override val width: UInt) :
  Btor2Sort(sid, width)
