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

sealed class C128(origin: CSimpleType?, parseContext: ParseContext) :
  CInteger(origin, parseContext) {
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

  private companion object {
    const val RANK = 60
  }
}

class CSigned128(origin: CSimpleType?, parseContext: ParseContext) :
  C128(origin, parseContext), Signed {

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)
}

class CUnsigned128(origin: CSimpleType?, parseContext: ParseContext) :
  C128(origin, parseContext), Unsigned {
  init {
    unsigned = true
  }

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)
}
