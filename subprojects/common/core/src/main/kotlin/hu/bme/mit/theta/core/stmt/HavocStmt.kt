/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * Havoc statement of the form `havoc VARIABLE`, which performs a non-deterministic assignment to
 * VARIABLE.
 *
 * @param <DeclType>
 */
@Serializable(with = HavocStmt.Serializer::class)
@SerialName(HavocStmt.STMT_LABEL)
data class HavocStmt<DeclType : Type>(val varDecl: VarDecl<DeclType>) : Stmt {

  companion object {

    internal const val STMT_LABEL = "havoc"

    @JvmStatic fun <T : Type> of(varDecl: VarDecl<T>): HavocStmt<T> = HavocStmt(varDecl)
  }

  override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R = visitor.visit(this, param)

  override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).add(varDecl.name).toString()

  object Serializer : KSerializer<HavocStmt<out Type>> {
    override val descriptor =
      buildClassSerialDescriptor("HavocStmt") { element<VarDecl<out Type>>("varDecl") }

    override fun serialize(encoder: Encoder, value: HavocStmt<out Type>) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, VarDecl.Serializer, value.varDecl)
      }

    override fun deserialize(decoder: Decoder): HavocStmt<out Type> =
      decoder.decodeStructure(descriptor) {
        var varDecl: VarDecl<out Type>? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 -> varDecl = decodeSerializableElement(descriptor, 0, VarDecl.Serializer)
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        HavocStmt(varDecl = varDecl ?: throw SerializationException("Missing varDecl"))
      }
  }
}
