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

import hu.bme.mit.theta.core.serialization.ExprReferenceSerializer
import hu.bme.mit.theta.core.serialization.ObjectTable
import hu.bme.mit.theta.core.serialization.TypeReferenceSerializer
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
import java.util.Objects
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient
import kotlinx.serialization.builtins.nullable
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

@Serializable
class CArray
@JvmOverloads
constructor(
  @Transient override val origin: CSimpleType? = null,
  @Serializable(with = CComplexTypeReferenceSerializer::class) val embeddedType: CComplexType,
  @Serializable(with = ParseContextSerializer::class) override val parseContext: ParseContext,
  /** If null, infinite */
  @Serializable(with = ArrayDimensionSerializer::class) val arrayDimension: CStatement? = null,
) : CInteger() {

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
      embeddedType == (other as CArray).embeddedType &&
      arrayDimension == other.arrayDimension

  override fun hashCode(): Int = Objects.hash(javaClass, embeddedType, arrayDimension)
}

/**
 * A parsed program only reads a dimension's expression, so that is what is kept of it; a dimension
 * without one reads back as none.
 */
@OptIn(ExperimentalSerializationApi::class)
object ArrayDimensionSerializer : KSerializer<CStatement?> {
  private val expression = ExprReferenceSerializer(TypeReferenceSerializer).nullable

  override val descriptor = SerialDescriptor("theta.ArrayDimension", expression.descriptor)

  override fun serialize(encoder: Encoder, value: CStatement?) =
    encoder.encodeSerializableValue(expression, value?.expression)

  override fun deserialize(decoder: Decoder): CStatement? =
    decoder.decodeSerializableValue(expression)?.let {
      CExpr(it, ObjectTable.current().ambient(ParseContext::class.java))
    }
}
