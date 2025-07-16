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
package hu.bme.mit.theta.frontend.visitors

import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.frontend.models.*
import hu.bme.mit.theta.frontend.models.Btor2Circuit.sorts
import java.math.BigInteger

class ConstantVisitor : Btor2BaseVisitor<Btor2Const>() {
  val idVisitor = IdVisitor()

  override fun visitConstantNode(ctx: Btor2Parser.ConstantNodeContext): Btor2Const {
    check(ctx.childCount == 1)
    return this.visit(ctx.children[0])
  }

  override fun visitConstant(ctx: Btor2Parser.ConstantContext): Btor2Const {
    val nid = idVisitor.visit(ctx.id)
    val sid = idVisitor.visit(ctx.sid())
    val sort: Btor2BitvecSort = sorts[sid] as Btor2BitvecSort
    val value = ctx.NUM().text.toString()
    val size = sort.width.toInt()
    val binArray = BooleanArray(size) { index -> (value[index] - '0') == 1 }
    var node = Btor2Const(nid, binArray, sort)
    Btor2Circuit.constants[nid] = node
    Btor2Circuit.nodes[nid] = node
    return node
  }

  override fun visitConstant_d(ctx: Btor2Parser.Constant_dContext): Btor2Const {
    val nid = idVisitor.visit(ctx.id)
    val sid = idVisitor.visit(ctx.sid())
    val sort: Btor2BitvecSort = sorts[sid] as Btor2BitvecSort
    val value = ctx.NUM().text.toBigInteger()
    val size = sort.width.toLong().toBigInteger()
    val binArray =
      BooleanArray(size.toInt()) { index ->
        ((value and ((BigInteger.ONE.shiftLeft(size.toInt())) - BigInteger.ONE)).shiftRight(
          size.toInt() - 1 - index
        ) and BigInteger.ONE) == BigInteger.ONE
      }
    var node = Btor2Const(nid, binArray, sort)
    Btor2Circuit.constants[nid] = node
    Btor2Circuit.nodes[nid] = node
    return node
  }

  override fun visitConstant_h(ctx: Btor2Parser.Constant_hContext): Btor2Const {
    val nid = idVisitor.visit(ctx.id)
    val sid = idVisitor.visit(ctx.sid())
    val sort: Btor2BitvecSort = sorts[sid] as Btor2BitvecSort
    val value = ctx.NUM().toString()
    val size = sort.width.toInt()
    val binArray =
      BooleanArray(size) { index ->
        val hexDigit = value[index / 4]
        val bitIndex = 3 - (index % 4)
        ((hexDigit - '0') shr bitIndex and 1) == 1
      }
    var node = Btor2Const(nid, binArray, sort)
    Btor2Circuit.constants[nid] = node
    Btor2Circuit.nodes[nid] = node
    return node
  }

  override fun visitFilled_constant(ctx: Btor2Parser.Filled_constantContext): Btor2Const {
    val nid = idVisitor.visit(ctx.id)
    val sid = idVisitor.visit(ctx.sid())
    val sort: Btor2BitvecSort = sorts[sid] as Btor2BitvecSort
    val value =
      when (ctx.fill.text) {
        "one" -> {
          val size = sort.width.toInt()
          BooleanArray(size) { it == size - 1 }
        }
        "ones" -> {
          val size = sort.width.toInt()
          BooleanArray(size) { true }
        }
        "zero" -> {
          val size = sort.width.toInt()
          BooleanArray(size) { false }
        }
        else -> {
          throw RuntimeException("Constant with filler shorthand needs to be one/ones/zero")
        }
      }
    var node = Btor2Const(nid, value, sort)
    Btor2Circuit.constants[nid] = node
    Btor2Circuit.nodes[nid] = node
    return node
  }
}
