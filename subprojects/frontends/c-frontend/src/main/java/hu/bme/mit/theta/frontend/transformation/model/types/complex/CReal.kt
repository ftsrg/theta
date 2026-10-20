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

import java.util.Objects
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable
sealed class CReal : CComplexType() {
  @Transient protected var rank = 0

  override fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)

  override fun width(): Int =
    parseContext.architecture.getBitWidth(typeName + "_s") +
      parseContext.architecture.getBitWidth(typeName + "_e")

  override fun getSmallestCommonType(type: CComplexType): CComplexType =
    if (type !is CReal || type.rank <= rank) this else type.getSmallestCommonType(this)

  override fun equals(other: Any?): Boolean = other != null && javaClass == other.javaClass

  override fun hashCode(): Int = Objects.hash(javaClass)
}
