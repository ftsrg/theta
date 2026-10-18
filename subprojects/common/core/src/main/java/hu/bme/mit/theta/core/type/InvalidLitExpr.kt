/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.type

import com.google.common.base.Preconditions.checkNotNull
import hu.bme.mit.theta.core.model.Valuation

class InvalidLitExpr<ExprType : Type>(type: ExprType) : NullaryExpr<ExprType>(), LitExpr<ExprType> {

  override val type: ExprType = checkNotNull(type)

  override fun eval(valuation: Valuation): LitExpr<ExprType> = this

  override val isInvalid: Boolean
    get() = true

  override fun equals(other: Any?): Boolean = false
}
