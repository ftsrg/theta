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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.*

/**
 * Assume statement of the form `[EXPRESSION]`, where EXPRESSION is a Boolean [Expr]. The statement
 * is a guard that can only be passed if EXPRESSION evaluates to true.
 */
@Serializable(with = AssumeStmt.Serializer::class)
@SerialName(AssumeStmt.STMT_LABEL)
data class AssumeStmt(val cond: Expr<BoolType>) : Stmt {

  companion object {

    internal const val STMT_LABEL = "assume"

    @JvmStatic fun of(cond: Expr<BoolType>): AssumeStmt = AssumeStmt(cond)

    @JvmStatic
    fun create(cond: Expr<*>): AssumeStmt {
      val newCond = cast(cond, Bool())
      return of(newCond)
    }
  }

  override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R = visitor.visit(this, param)

  override fun toString(): String = Utils.lispStringBuilder(STMT_LABEL).add(cond).toString()

  object Serializer : KSerializer<AssumeStmt> {
    override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("AssumeStmt") { element<Expr<BoolType>>("cond") }

    override fun serialize(encoder: Encoder, value: AssumeStmt) =
      encoder.encodeStructure(descriptor) {
        encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class), value.cond)
      }

    override fun deserialize(decoder: Decoder): AssumeStmt =
      decoder.decodeStructure(descriptor) {
        var cond: Expr<BoolType>? = null
        while (true) {
          when (val i = decodeElementIndex(descriptor)) {
            0 ->
              cond =
                decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Expr::class))
                  as Expr<BoolType>
            CompositeDecoder.DECODE_DONE -> break
            else -> throw SerializationException("Unknown index $i")
          }
        }
        AssumeStmt(cond = cond ?: throw SerializationException("Missing cond"))
      }
  }
}
