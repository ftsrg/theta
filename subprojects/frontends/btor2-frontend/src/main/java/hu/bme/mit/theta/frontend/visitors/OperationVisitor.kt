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
import hu.bme.mit.theta.frontend.models.Btor2Circuit.nodes
import kotlin.math.abs

class OperationVisitor : Btor2BaseVisitor<Btor2Node>() {
    val idVisitor = IdVisitor()
    override fun visitOperation(ctx: Btor2Parser.OperationContext): Btor2Node {
        check(ctx.childCount == 1)
        return ctx.children[0].accept(this)
    }

    override fun visitExt(ctx: Btor2Parser.ExtContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BitvecSort = Btor2Circuit.sorts[sid] as Btor2BitvecSort
        val op = when (ctx.operator.text) {
            "sext" -> Btor2ExtOperator.SEXT
            "uext" -> Btor2ExtOperator.UEXT
            else -> throw RuntimeException("Extension operator unknown")
        }

        val opd = nodes[ctx.opd1.text.toUInt()] as Btor2Node
        val w = ctx.w.text.toUInt()

        check(sort.width == (opd.sort as Btor2BitvecSort).width + w)
        val node =  Btor2ExtOperation(nid, sort, op, opd, w)
        Btor2Circuit.nodes[nid] = node
        Btor2Circuit.ops[nid] = node
        return node
    }

    override fun visitSlice(ctx: Btor2Parser.SliceContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BitvecSort = Btor2Circuit.sorts[sid] as Btor2BitvecSort

        val opd = nodes[ctx.opd1.text.toUInt()] as Btor2Node
        val u = ctx.u.text.toBigInteger()
        val l = ctx.l.text.toBigInteger()

        val node =  Btor2SliceOperation(nid, sort, opd, u, l)
        Btor2Circuit.nodes[nid] = node
        Btor2Circuit.ops[nid] = node
        return node
    }

    override fun visitBinop(ctx: Btor2Parser.BinopContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BitvecSort = Btor2Circuit.sorts[sid] as Btor2BitvecSort

        val opd1_id = ctx.opd1.text.toInt()
        val opd2_id = ctx.opd2.text.toInt()

        val opd1_negated = opd1_id < 0
        val opd2_negated = opd2_id < 0

        val opd1 = nodes[abs(opd1_id).toUInt()] as Btor2Node
        val opd2 = nodes[abs(opd2_id).toUInt()] as Btor2Node

        val op = when (ctx.BINOP().text) {
            "and" -> Btor2BinaryOperator.AND
            "nand" -> Btor2BinaryOperator.NAND
            "nor" -> Btor2BinaryOperator.NOR
            "or" -> Btor2BinaryOperator.OR
            "xnor" -> Btor2BinaryOperator.XNOR
            "xor" -> Btor2BinaryOperator.XOR
            "add" -> Btor2BinaryOperator.ADD
            "mul" -> Btor2BinaryOperator.MUL
            "sub" -> Btor2BinaryOperator.SUB
            "udiv" -> Btor2BinaryOperator.UDIV
            "urem" -> Btor2BinaryOperator.UREM
            "sdiv" -> Btor2BinaryOperator.SDIV
            "srem" -> Btor2BinaryOperator.SREM
            "smod" -> Btor2BinaryOperator.SMOD
            "concat" -> Btor2BinaryOperator.CONCAT
            "saddo" -> Btor2BinaryOperator.SADDO
            "sdivo" -> Btor2BinaryOperator.SDIVO
            "smulo" -> Btor2BinaryOperator.SMULO
            "ssubo" -> Btor2BinaryOperator.SSUBO
            "uaddo" -> Btor2BinaryOperator.UADDO
            "umulo" -> Btor2BinaryOperator.UMULO
            "usubo" -> Btor2BinaryOperator.USUBO
            "rol" -> Btor2BinaryOperator.ROL
            "ror" -> Btor2BinaryOperator.ROR
            "sll" -> Btor2BinaryOperator.SLL
            "sra" -> Btor2BinaryOperator.SRA
            "srl" -> Btor2BinaryOperator.SRL
            "eq" -> Btor2ComparisonOperator.EQ
            "neq" -> Btor2ComparisonOperator.NEQ
            "slt" -> Btor2ComparisonOperator.SLT
            "slte" -> Btor2ComparisonOperator.SLTE
            "sgt" -> Btor2ComparisonOperator.SGT
            "sgte" -> Btor2ComparisonOperator.SGTE
            "ult" -> Btor2ComparisonOperator.ULT
            "ulte" -> Btor2ComparisonOperator.ULTE
            "ugt" -> Btor2ComparisonOperator.UGT
            "ugte" -> Btor2ComparisonOperator.UGTE
            else -> throw RuntimeException("Binary operator unknown")
        }
        if (op is Btor2ComparisonOperator) {
            val node =  Btor2Comparison(nid, sort, op, opd1, opd2, opd1_negated, opd2_negated)
            Btor2Circuit.nodes[nid] = node
            return node
        }
        else if (op is Btor2BinaryOperator) {
            val node =  Btor2BinaryOperation(nid, sort, op, opd1, opd2, opd1_negated, opd2_negated)
            Btor2Circuit.nodes[nid] = node
            Btor2Circuit.ops[nid] = node
            return node
        }
        else {
            throw RuntimeException("Binary operator unknown")
        }
    }

    override fun visitUnop(ctx: Btor2Parser.UnopContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BitvecSort = Btor2Circuit.sorts[sid] as Btor2BitvecSort

        val op = when (ctx.UNARYOP().text) {
            "not" -> Btor2UnaryOperator.NOT
            "inc" -> Btor2UnaryOperator.INC
            "dec" -> Btor2UnaryOperator.DEC
            "neg" -> Btor2UnaryOperator.NEG
            "redand" -> Btor2UnaryOperator.REDAND
            "redor" -> Btor2UnaryOperator.REDOR
            "redxor" -> Btor2UnaryOperator.REDXOR
            else -> throw RuntimeException("Unary operator unknown")
        }

        val opd = nodes[ctx.opd1.text.toUInt()] as Btor2Node


        val node =  Btor2UnaryOperation(nid, sort, op, opd)
        Btor2Circuit.nodes[nid] = node
        Btor2Circuit.ops[nid] = node
        return node
    }

    override fun visitTerop(ctx: Btor2Parser.TeropContext): Btor2Node {
        val nid = idVisitor.visit(ctx.id)
        val sid = idVisitor.visit(ctx.sid())
        val sort : Btor2BitvecSort = Btor2Circuit.sorts[sid] as Btor2BitvecSort
        val op = when (ctx.TERNARYOP().text) {
            "ite" -> Btor2TernaryOperator.ITE
            "write" -> Btor2TernaryOperator.WRITE
            else -> throw RuntimeException("Ternary operator unknown")
        }
        val negated1 = ctx.opd1.text.toInt() < 0
        val opd1Index = abs(ctx.opd1.text.toInt()).toUInt()
        val negated2 = ctx.opd2.text.toInt() < 0
        val negated3 = ctx.opd3.text.toInt() < 0
        val opd2Index = abs(ctx.opd2.text.toInt()).toUInt()
        val opd3Index = abs(ctx.opd3.text.toInt()).toUInt()

        val opd1 = nodes[opd1Index] as Btor2Node
        val opd2 = nodes[opd2Index] as Btor2Node
        val opd3 = nodes[opd3Index] as Btor2Node

        val node =  Btor2TernaryOperation(nid, sort, op, opd1, opd2, opd3, negated1, negated2, negated3)
        Btor2Circuit.nodes[nid] = node
        Btor2Circuit.ops[nid] = node
        return node
    }
}