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
@file:Suppress("UNUSED_PARAMETER")

package hu.bme.mit.theta.core.serialization

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.functype.FuncType
import kotlinx.serialization.KSerializer
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

// A class with identity names one of these in @Serializable(with = ...): its properties are written
// as ObjectTable indices, and @KeepGeneratedSerializer keeps the serializer of the object itself.
// A generic class's one is handed its type arguments' serializers, which a reference ignores.

/** Marks the serializers that write an index into the [ObjectTable] instead of the object. */
interface ReferenceSerializer

abstract class AbstractReferenceSerializer<T : Any>(name: String, private val cls: Class<*>) :
  KSerializer<T>, ReferenceSerializer {
  override val descriptor: SerialDescriptor = PrimitiveSerialDescriptor(name, PrimitiveKind.INT)

  override fun serialize(encoder: Encoder, value: T) =
    encoder.encodeInt(ObjectTable.current().idOf(value))

  @Suppress("UNCHECKED_CAST")
  override fun deserialize(decoder: Decoder): T {
    val value = ObjectTable.current().valueAt(decoder.decodeInt())
    check(cls.isInstance(value)) { "Expected a ${cls.simpleName} reference, found $value" }
    return value as T
  }
}

object TypeReferenceSerializer :
  AbstractReferenceSerializer<Type>("theta.TypeRef", Type::class.java)

class ArrayTypeReferenceSerializer<I, E>(index: KSerializer<I>, elem: KSerializer<E>) :
  AbstractReferenceSerializer<ArrayType<*, *>>("theta.ArrayTypeRef", ArrayType::class.java)

class FuncTypeReferenceSerializer<P, R>(param: KSerializer<P>, result: KSerializer<R>) :
  AbstractReferenceSerializer<FuncType<*, *>>("theta.FuncTypeRef", FuncType::class.java)

class DeclReferenceSerializer<T>(type: KSerializer<T>) :
  AbstractReferenceSerializer<Decl<*>>("theta.DeclRef", Decl::class.java)

class ExprReferenceSerializer<T>(type: KSerializer<T>) :
  AbstractReferenceSerializer<Expr<*>>("theta.ExprRef", Expr::class.java)

object StmtReferenceSerializer :
  AbstractReferenceSerializer<Stmt>("theta.StmtRef", Stmt::class.java)

/**
 * An object that everything in the table shares (see [ObjectTable.ambient]): it is not written,
 * decoding takes the table's own. A marker is written so that every format keeps the property.
 */
abstract class AmbientSerializer<T : Any>(name: String, private val cls: Class<T>) :
  KSerializer<T> {
  override val descriptor: SerialDescriptor = PrimitiveSerialDescriptor(name, PrimitiveKind.INT)

  override fun serialize(encoder: Encoder, value: T) {
    check(value === ObjectTable.current().ambient(cls)) {
      "${cls.simpleName} $value is not the one this table was made with"
    }
    encoder.encodeInt(0)
  }

  override fun deserialize(decoder: Decoder): T {
    decoder.decodeInt()
    return ObjectTable.current().ambient(cls)
  }
}
