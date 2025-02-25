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

import gen.Btor2BaseVisitor
import gen.Btor2Parser
import hu.bme.mit.theta.frontend.models.*
import hu.bme.mit.theta.frontend.models.Btor2Circuit.sorts

class ConstantVisitor : Btor2BaseVisitor<Btor2Const>() {
    val idVisitor = IdVisitor()

    override fun visitConstantNode(ctx: Btor2Parser.ConstantNodeContext): Btor2Const {
        check(ctx.childCount==1)
        return this.visit(ctx.children[0])
    }
    override fun visitFilled_constant(ctx: Btor2Parser.Filled_constantContext): Btor2Const {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BitvecSort = sorts[sid] as Btor2BitvecSort
        val value = when(ctx.fill.text) {
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
        Btor2Circuit.nodes[nid] = node
        return node
    }
}