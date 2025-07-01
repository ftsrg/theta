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

/** Represents a type that supports ordering and comparison operations. */
@Polymorphic
interface Ordered<OpType : Ordered<OpType>> : Type {
  fun Lt(leftOp: Expr<OpType>, rightOp: Expr<OpType>): LtExpr<OpType>

  fun Leq(leftOp: Expr<OpType>, rightOp: Expr<OpType>): LeqExpr<OpType>

  fun Gt(leftOp: Expr<OpType>, rightOp: Expr<OpType>): GtExpr<OpType>

  fun Geq(leftOp: Expr<OpType>, rightOp: Expr<OpType>): GeqExpr<OpType>
}
