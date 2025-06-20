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

package hu.bme.mit.theta.core.type.inttype

import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.*
import hu.bme.mit.theta.core.type.rattype.RatType
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName(IntType.TYPE_LABEL)
object IntType : Additive<IntType>, Multiplicative<IntType>, Divisible<IntType>, Equational<IntType>, Ordered<IntType>,
    Castable<IntType> {

    internal const val TYPE_LABEL = "Int"
    fun getInstance(): IntType = this
    override fun toString(): String = TYPE_LABEL

    override fun Add(ops: Iterable<Expr<IntType>>) = IntExprs.Add(ops)
    override fun Sub(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntExprs.Sub(leftOp, rightOp)
    override fun Pos(op: Expr<IntType>) = IntExprs.Pos(op)
    override fun Neg(op: Expr<IntType>) = IntExprs.Neg(op)
    override fun Mul(ops: Iterable<Expr<IntType>>) = IntExprs.Mul(ops)
    override fun Div(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntExprs.Div(leftOp, rightOp)
    override fun Mod(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntExprs.Mod(leftOp, rightOp)
    override fun Rem(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntExprs.Rem(leftOp, rightOp)
    override fun Eq(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntExprs.Eq(leftOp, rightOp)
    override fun Neq(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntExprs.Neq(leftOp, rightOp)
    override fun Lt(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntExprs.Lt(leftOp, rightOp)
    override fun Leq(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntExprs.Leq(leftOp, rightOp)
    override fun Gt(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntExprs.Gt(leftOp, rightOp)
    override fun Geq(leftOp: Expr<IntType>, rightOp: Expr<IntType>) = IntExprs.Geq(leftOp, rightOp)
    @Suppress("UNCHECKED_CAST")
    override fun <TargetType : Type> Cast(op: Expr<IntType>, type: TargetType): Expr<TargetType> =
        if (type is RatType) IntExprs.ToRat(op) as Expr<TargetType>
        else throw ClassCastException("Int cannot be cast to $type")

    override val domainSize: DomainSize = DomainSize.INFINITY
}

