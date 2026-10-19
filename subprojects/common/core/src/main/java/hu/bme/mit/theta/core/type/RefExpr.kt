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
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.model.Valuation

class RefExpr<DeclType : Type> private constructor(decl: Decl<DeclType>) : NullaryExpr<DeclType>() {

  val decl: Decl<DeclType> = checkNotNull(decl)

  @Volatile private var hashCode = 0

  override val type: DeclType
    get() = decl.type

  override fun eval(valuation: Valuation): LitExpr<DeclType> =
    valuation.eval(decl).orElseThrow {
      NoSuchElementException(
        "No value for '${decl.name}' of type ${decl.type} in the valuation; an expression" +
          " containing it was evaluated against a valuation that does not bind it."
      )
    }

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + decl.hashCode()
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    this === other ||
      (other != null && javaClass == other.javaClass && decl == (other as RefExpr<*>).decl)

  override fun toString(): String = decl.name

  companion object {
    private const val HASH_SEED = 167

    @JvmStatic fun <DeclType : Type> of(decl: Decl<DeclType>): RefExpr<DeclType> = RefExpr(decl)
  }
}
