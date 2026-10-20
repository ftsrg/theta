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

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.serialization.DeclReferenceSerializer
import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.SerializationException
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.encoding.CompositeDecoder
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.encoding.decodeStructure
import kotlinx.serialization.encoding.encodeStructure

@Serializable(with = RefExprSerializer::class)
class RefExpr<DeclType : Type> private constructor(val decl: Decl<DeclType>) :
  NullaryExpr<DeclType>() {

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
    if (other is TraceableWrapperExpr<*>) equals(other.expr)
    else
      this === other ||
        (other != null && javaClass == other.javaClass && decl == (other as RefExpr<*>).decl)

  override fun toString(): String = decl.name

  companion object {
    private const val HASH_SEED = 167

    @JvmStatic fun <DeclType : Type> of(decl: Decl<DeclType>): RefExpr<DeclType> = RefExpr(decl)
  }
}

/**
 * A reference keeps whether it is its declaration's canonical [Decl.ref]: code compares against
 * that object by identity.
 */
class RefExprSerializer<T>(type: KSerializer<T>) : KSerializer<RefExpr<*>> {
  private val decl = DeclReferenceSerializer(type)

  override val descriptor: SerialDescriptor =
    buildClassSerialDescriptor("theta.RefExpr") {
      element("decl", decl.descriptor)
      element("canonical", Boolean.serializer().descriptor)
    }

  override fun serialize(encoder: Encoder, value: RefExpr<*>) =
    encoder.encodeStructure(descriptor) {
      encodeSerializableElement(descriptor, 0, decl, value.decl)
      encodeBooleanElement(descriptor, 1, value === value.decl.ref)
    }

  override fun deserialize(decoder: Decoder): RefExpr<*> =
    decoder.decodeStructure(descriptor) {
      var d: Decl<*>? = null
      var canonical = false
      while (true) {
        when (val index = decodeElementIndex(descriptor)) {
          0 -> d = decodeSerializableElement(descriptor, 0, decl)
          1 -> canonical = decodeBooleanElement(descriptor, 1)
          CompositeDecoder.DECODE_DONE -> break
          else -> throw SerializationException("Unexpected RefExpr element $index")
        }
      }
      val resolved = checkNotNull(d) { "A RefExpr needs its declaration" }
      if (canonical) resolved.ref else RefExpr.of(resolved)
    }
}
