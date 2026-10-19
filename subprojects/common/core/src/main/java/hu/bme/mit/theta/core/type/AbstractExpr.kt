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

/** Common base of all expressions; holds the [sourceType] slot. */
sealed class AbstractExpr<ExprType : Type> : Expr<ExprType>, Cloneable {

  final override var sourceType: SourceType? = null
    private set

  override fun withSourceType(sourceType: SourceType?): Expr<ExprType> {
    if (sourceType === this.sourceType) return this
    // Expressions are immutable, so a shallow copy shares the operands and the cached hash code.
    @Suppress("UNCHECKED_CAST") val copy = clone() as AbstractExpr<ExprType>
    copy.sourceType = sourceType
    return copy
  }

  /** [rewritten], which replaces this expression's operands, with this expression's source type. */
  protected fun <E : Expr<*>> keepSourceType(rewritten: E): E {
    val sourceType = sourceType
    if (sourceType == null || rewritten === this || rewritten.sourceType != null) return rewritten
    @Suppress("UNCHECKED_CAST") return rewritten.withSourceType(sourceType) as E
  }
}
