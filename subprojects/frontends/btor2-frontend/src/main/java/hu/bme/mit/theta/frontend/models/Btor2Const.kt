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
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr


abstract class Btor2Const<T>(
    override val nid: UInt,
    open val value: T,
    override val sort: Btor2Sort
) : Btor2Node(nid, sort)

data class Btor2Const_b(
    override val nid: UInt,
    override val value: BooleanArray,
    override val sort: Btor2Sort
) : Btor2Const<BooleanArray>(nid, value, sort) {
    override fun getVar(): VarDecl<*>? {
        return null
    }

    override fun getExpr(): Expr<*> {
        return BvLitExpr.of(value)
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}

data class Btor2Const_d(
    override val nid: UInt,
    override val value: Int,
    override val sort: Btor2Sort
) : Btor2Const<Int>(nid, value, sort)
{
    override fun getVar(): VarDecl<*>? {
        return null
    }

    override fun getExpr(): Expr<*> {
        val size = sort.width.toInt()
        val bin_array = BooleanArray(size) { index ->
            (value shr (size - 1 - index)) and 1 == 1
        }
        return BvLitExpr.of(bin_array)
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}

data class Btor2Const_h(
    override val nid: UInt,
    override val value: String,
    override val sort: Btor2Sort
) : Btor2Const<String>(nid, value, sort)
{
    override fun getVar(): VarDecl<*>? {
        return null
    }

    override fun getExpr(): Expr<*> {
        // return BvLitExpr.of(value)
        TODO("Hexadecimal literal parsing not implemented")
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }
}