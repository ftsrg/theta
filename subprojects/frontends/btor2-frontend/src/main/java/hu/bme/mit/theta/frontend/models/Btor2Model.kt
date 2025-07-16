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
  var nodes: MutableMap<UInt, Btor2Node> = mutableMapOf()
  var sorts: MutableMap<UInt, Btor2Sort> = mutableMapOf()
  var constants: MutableMap<UInt, Btor2Const> = mutableMapOf()
  var ops: MutableMap<UInt, Btor2Operation> = mutableMapOf()
  var states: MutableMap<UInt, Btor2Stateful> = mutableMapOf()
  var properties: MutableMap<UInt, Btor2Bad> = mutableMapOf()
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
