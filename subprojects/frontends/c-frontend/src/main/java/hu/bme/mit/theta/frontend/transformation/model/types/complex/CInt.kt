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

sealed class CInt(origin: CSimpleType?, parseContext: ParseContext) :
  CInteger(origin, parseContext) {
  init {
    rank = RANK
  }

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)

  override val typeName: String
    get() = "int"

  override val signedVersion: CInteger
    get() = CSignedInt(null, parseContext)

  override val unsignedVersion: CInteger
    get() = CUnsignedInt(null, parseContext)

  private companion object {
    const val RANK = 30
  }
}

class CSignedInt(origin: CSimpleType?, parseContext: ParseContext) :
  CInt(origin, parseContext), Signed {

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)
}

class CUnsignedInt(origin: CSimpleType?, parseContext: ParseContext) :
  CInt(origin, parseContext), Unsigned {
  init {
    unsigned = true
  }

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)
}
