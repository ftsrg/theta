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
package hu.bme.mit.theta.frontend.transformation.model.types.complex

import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Signed
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Unsigned
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable
sealed class C128 : CInteger() {
  init {
    rank = RANK
  }

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)

  override val typeName: String
    get() = "__int128"

  override val signedVersion: CInteger
    get() = CSigned128(null, parseContext)

  override val unsignedVersion: CInteger
    get() = CUnsigned128(null, parseContext)

  companion object {
    private const val RANK = 60
  }
}

@Serializable
class CSigned128(
  @Transient override val origin: CSimpleType? = null,
  @Serializable(with = ParseContextSerializer::class) override val parseContext: ParseContext,
) : C128(), Signed {

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)
}

@Serializable
class CUnsigned128(
  @Transient override val origin: CSimpleType? = null,
  @Serializable(with = ParseContextSerializer::class) override val parseContext: ParseContext,
) : C128(), Unsigned {
  init {
    unsigned = true
  }

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)
}
