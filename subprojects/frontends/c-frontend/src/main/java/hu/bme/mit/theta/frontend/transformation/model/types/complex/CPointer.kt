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
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
import java.util.Objects

class CPointer(origin: CSimpleType?, val embeddedType: CComplexType?, parseContext: ParseContext) :
  CInteger(origin, parseContext) {

  /**
   * True when this pointer holds a function's address (id) rather than a data-object address, so
   * that a call through it is dispatched over the candidate set. Carried on the TYPE (not just on a
   * variable) so that function pointers stored in struct fields, arrays and typedefs are recognized
   * too.
   */
  var isFunctionPointer = false

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)

  override val signedVersion: CInteger
    get() = this

  override val unsignedVersion: CInteger
    get() = this

  override val typeName: String
    get() = CUnsignedLong(null, parseContext).typeName

  override fun equals(other: Any?): Boolean =
    other != null &&
      javaClass == other.javaClass &&
      embeddedType == (other as CPointer).embeddedType

  override fun hashCode(): Int = Objects.hash(javaClass, embeddedType)
}
