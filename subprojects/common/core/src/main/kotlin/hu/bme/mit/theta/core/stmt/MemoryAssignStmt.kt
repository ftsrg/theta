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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * Assignment statement of the form `*(DEREF_EXPRESSION) := EXPRESSION`. The statement updates the
 * value pointed to by DEREF_EXPRESSION with the result of EXPRESSION.
 *
 * @param PtrType The type of the pointer
 * @param OffsetType The type of the offset
 * @param DeclType The type of the value being assigned
 */
@Serializable(with = MemoryAssignStmt.Serializer::class)
@SerialName(MemoryAssignStmt.STMT_LABEL)
data class MemoryAssignStmt<PtrType : Type, OffsetType : Type, DeclType : Type>(
  val deref: Dereference<PtrType, OffsetType, DeclType>,
  val expr: Expr<DeclType>,
) : Stmt {

  companion object {

    internal const val STMT_LABEL = "memassign"

    @JvmStatic
    fun <PtrType : Type, OffsetType : Type, DeclType : Type> of(
      deref: Dereference<PtrType, OffsetType, DeclType>,
      expr: Expr<DeclType>,
    ): MemoryAssignStmt<PtrType, OffsetType, DeclType> = MemoryAssignStmt(deref, expr)

    @JvmStatic
    @Suppress("UNCHECKED_CAST")
    fun <PtrType : Type, OffsetType : Type, DeclType : Type> create(
      deref: Dereference<PtrType, OffsetType, *>,
      expr: Expr<DeclType>,
    ): MemoryAssignStmt<PtrType, OffsetType, DeclType> {
      val typedDeref = deref as Dereference<PtrType, OffsetType, DeclType>
      return of(typedDeref, expr)
    }
  }

  override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R = visitor.visit(this, param)

  override fun toString(): String =
    Utils.lispStringBuilder(STMT_LABEL).add(deref).add(expr).toString()

  object Serializer : KSerializer<MemoryAssignStmt<out Type, out Type, out Type>> {
    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("MemoryAssignStmt") {
        element<Dereference<out Type, out Type, out Type>>("deref")
        element<Expr<out Type>>("expr")
      }

    override fun serialize(
      encoder: Encoder,
      value: MemoryAssignStmt<out Type, out Type, out Type>,
    ) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, Dereference.Serializer, value.deref)
        encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class), value.expr)
      }

    override fun deserialize(decoder: Decoder): MemoryAssignStmt<out Type, out Type, out Type> =
      decoder.decodeStructure(descriptor) {
        var deref: Dereference<out Type, out Type, Type>? = null
        var expr: Expr<Type>? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 ->
              deref =
                decodeSerializableElement(descriptor, 0, Dereference.Serializer)
                  as Dereference<out Type, out Type, Type>
            1 ->
              expr =
                decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Expr::class))
                  as Expr<Type>
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        MemoryAssignStmt(
          deref ?: throw SerializationException("Missing deref "),
          expr ?: throw SerializationException("Missing expr "),
        )
      }
  }
}
