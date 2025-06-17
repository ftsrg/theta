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

package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.Polymorphic

@Polymorphic
abstract class Additive<ExprType : Additive<ExprType>> : Type {

    abstract fun Add(ops: Iterable<Expr<ExprType>>): AddExpr<ExprType>

    abstract fun Sub(leftOp: Expr<ExprType>, rightOp: Expr<ExprType>): SubExpr<ExprType>

    abstract fun Pos(op: Expr<ExprType>): PosExpr<ExprType>

    abstract fun Neg(op: Expr<ExprType>): NegExpr<ExprType>
}
