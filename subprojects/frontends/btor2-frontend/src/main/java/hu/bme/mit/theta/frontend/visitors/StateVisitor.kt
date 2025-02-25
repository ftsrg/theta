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

class StateVisitor : Btor2BaseVisitor<Btor2Node>() {
    private val idVisitor = IdVisitor()

    override fun visitStateful(ctx: Btor2Parser.StatefulContext): Btor2Node {
        check(ctx.childCount==1)
        return ctx.children[0].accept(this)
    }

    override fun visitState(ctx: Btor2Parser.StateContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort = Btor2Circuit.sorts[sid] as Btor2Sort

        val node = Btor2State(nid, sort)
        Btor2Circuit.nodes[nid] = node
        return node
    }

    override fun visitInput(ctx: Btor2Parser.InputContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort = Btor2Circuit.sorts[sid] as Btor2Sort

        val node = Btor2Input(nid, sort)
        Btor2Circuit.nodes[nid] = node
        return node
    }

    override fun visitInit(ctx: Btor2Parser.InitContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort = Btor2Circuit.sorts[sid]!!

        val param1 = Btor2Circuit.nodes[ctx.param1.NUM().text.toUInt()] as Btor2State
        val param2 = Btor2Circuit.nodes[ctx.param2.NUM().text.toUInt()] as Btor2Const


        check((param1.sort as Btor2BitvecSort).width == (param2.sort as Btor2BitvecSort).width)
        val node = Btor2Init(nid, sort, param1, param2)
        Btor2Circuit.inits[nid] = node
        return node
    }

    override fun visitNext(ctx: Btor2Parser.NextContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort = Btor2Circuit.sorts[sid] as Btor2Sort

        val param1 = Btor2Circuit.nodes[ctx.param1.NUM().text.toUInt()] as Btor2State
        val param2 = Btor2Circuit.nodes[ctx.param2.NUM().text.toUInt()] as Btor2Node
        val node = Btor2Next(nid, sort, param1, param2)
        Btor2Circuit.nexts[nid] = node
        Btor2Circuit.nodes[nid] = node
        return node
    }

    override fun visitProperty(ctx: Btor2Parser.PropertyContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val node = Btor2Bad(nid, null, Btor2Circuit.nodes[ctx.param.NUM().text.toUInt()] as Btor2Node)
        Btor2Circuit.bads[nid] = node
        Btor2Circuit.nodes[nid] = node
        return node
    }
}