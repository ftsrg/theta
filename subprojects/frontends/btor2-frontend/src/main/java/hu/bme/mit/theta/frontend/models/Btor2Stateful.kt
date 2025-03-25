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

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvType

abstract class Btor2Stateful(id: UInt, sort: Btor2Sort, state: Btor2State?, value: Btor2Node?) : Btor2Node(id, sort) {
    abstract val state: Btor2State?
    abstract val value: Btor2Node?
}

// Inputs and States
data class Btor2Input(override val nid: UInt, override val sort: Btor2Sort, override val state: Btor2State?,
    override val value: Btor2Node?) : Btor2Stateful(nid, sort,null,null)
{
    val declsVar = Decls.Var("input_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return declsVar
    }

    override fun getExpr(): Expr<*> {
        return RefExpr.of(declsVar) // Valamilyen Bool type kellene? nem
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

}
data class Btor2State(override val nid: UInt, override val sort: Btor2Sort, override val state: Btor2State?,
    override val value: Btor2Node?) : Btor2Stateful(nid, sort,null,null) {
    val declsVar = Decls.Var("state_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<BvType>? {
        return declsVar
    }

    override fun getExpr(): Expr<*> {
        return RefExpr.of(declsVar)
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}
// Value was Btor2Const
data class Btor2Init(override val nid: UInt, override val sort: Btor2Sort, override val state: Btor2State,
    override val value: Btor2Node) : Btor2Stateful(nid, sort, state, value)
{
    val declsVar = Decls.Var("init_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return declsVar
    }

    override fun getExpr(): Expr<*> {
        TODO("Not yet implemented")
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}

data class Btor2Next(override val nid: UInt, override val sort: Btor2Sort, override val state: Btor2State, override val value: Btor2Node) : Btor2Stateful(nid, sort, state, value)
{
    val declsVar = Decls.Var("next_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return declsVar
    }

    override fun getExpr(): Expr<*> {
        return RefExpr.of(declsVar)
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}
