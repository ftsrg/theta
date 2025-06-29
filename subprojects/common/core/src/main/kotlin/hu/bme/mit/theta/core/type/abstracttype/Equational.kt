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

/**
 * Represents a type that supports equational operations.
 *
 * @param OpType The type of the operands, which must also be equational.
 */
@Polymorphic
interface Equational<OpType : Equational<OpType>> : Type {

  fun Eq(leftOp: Expr<OpType>, rightOp: Expr<OpType>): EqExpr<OpType>

  fun Neq(leftOp: Expr<OpType>, rightOp: Expr<OpType>): NeqExpr<OpType>
}
