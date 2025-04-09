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
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvEqExpr
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Eq
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType

//abstract class Btor2Properties(override val nid: UInt, override val sort: Btor2Sort?, open val operand: Btor2Node) : Btor2Node(nid, null)
//{
//
//}
data class Btor2Bad(override val nid: UInt, override val sort: Btor2Sort?, val operand: Btor2Node) : Btor2Node(nid, null)
{
    override fun getVar(): VarDecl<*>? {
        return null
    }

    override fun getExpr(): Expr<BoolType> {
        return Eq(operand.getVar()?.ref as RefExpr<BvType>, BvExprs.Bv(BooleanArray(1, {true})))
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}
//
//data class Btor2Constraint(override val nid: UInt, override val sort: Btor2Sort?, override val operand: Btor2Node) : Btor2Properties(nid, null, operand)
//{
//    override fun getVar(): VarDecl<*>? {
//        return null
//    }
//
//    override fun getExpr(): Expr<*> {
//        TODO()
//    }
//
//
//    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
//        return visitor.visit(this, param)
//    }
//}
//
//data class Btor2Fair(override val nid: UInt, override val sort: Btor2Sort?, override val operand: Btor2Node) : Btor2Properties(nid, null, operand)
//{
//    override fun getVar(): VarDecl<*>? {
//        return null
//    }
//
//    override fun getExpr(): Expr<*> {
//        TODO()
//    }
//
//    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
//        return visitor.visit(this, param)
//    }
//}
//
//data class Btor2Output(override val nid: UInt, override val sort: Btor2Sort?, override val operand: Btor2Node) : Btor2Properties(nid, null, operand)
//{
//    override fun getVar(): VarDecl<*>? {
//        return null
//    }
//
//    override fun getExpr(): Expr<*> {
//        TODO()
//    }
//
//
//
//    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
//        return visitor.visit(this, param)
//    }
//}
// <nid> 'justice' <num> (<nid>)+ Szóval még hagyjuk <3
// TODO: justice
//data class Btor2Justice(override val nid: UInt, override val sort: Btor2Sort?, override val operand: Btor2Node) : Btor2Properties(nid, null, operand)
//{
//    override fun getVar(): VarDecl<*>? {
//        return null
//    }
//
//    override fun getExpr(): Expr<*> {
//        TODO()
//    }
//
//    override fun getExpr(negate: Boolean): Expr<*>? {
//        TODO()
//    }
//
//   override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
//        return visitor.visit(this, param)
//    }
//}