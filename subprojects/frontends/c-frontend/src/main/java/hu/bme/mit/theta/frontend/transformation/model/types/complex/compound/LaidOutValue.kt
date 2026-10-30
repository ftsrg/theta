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
package hu.bme.mit.theta.frontend.transformation.model.types.complex.compound

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.TraceabilityInfo
import hu.bme.mit.theta.core.type.TraceableWrapperExpr
import hu.bme.mit.theta.core.type.traceabilityInfo
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexTypeReferenceSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * A value read out of storage that several values share (see [BitfieldSlice], [ByteUnionSlice]):
 * its C type, and where it was read from, which an assignment through it needs to write that
 * storage back. An expression rebuilt from it is no longer that read, so it keeps only the type.
 */
@Serializable
@SerialName("laidOut")
data class LaidOutValue(
  @Serializable(with = CComplexTypeReferenceSerializer::class) val cType: CComplexType,
  val origin: StorageOrigin,
) : TraceabilityInfo {

  override fun afterRewrite(): TraceabilityInfo = cType

  companion object {
    /** [value] typed [type], read from [origin]. */
    @JvmStatic
    fun <T : hu.bme.mit.theta.core.type.Type> of(
      value: Expr<T>,
      type: CComplexType,
      origin: StorageOrigin,
    ): Expr<T> = TraceableWrapperExpr.of(value, LaidOutValue(type, origin))

    /** Where [expr] itself (not a subexpression) was read from, if it is such a read. */
    @JvmStatic
    fun originOf(expr: Expr<*>): StorageOrigin? = (expr.traceabilityInfo as? LaidOutValue)?.origin
  }
}

/** Where a [LaidOutValue] was read from. */
@Serializable
sealed interface StorageOrigin {

  /**
   * The [width]-bit field at [bitOffset] of [cell]. With [ieeeFloat], the cell holds a float's raw
   * IEEE-754 bit pattern: the read reinterprets it, and a write splices in the bits of the value.
   */
  @Serializable
  @SerialName("bitfield")
  data class Bitfield(
    val cell: Expr<*>,
    val bitOffset: Int,
    val width: Int,
    val ieeeFloat: Boolean,
  ) : StorageOrigin

  /**
   * The cell of a union member that is one packed unit of bitfields (see `CStruct#isPackedScalar`):
   * a member of it slices this cell instead of dereferencing it again.
   */
  @Serializable @SerialName("packedCell") data object PackedCell : StorageOrigin

  /**
   * A [widthBytes]-byte member at byte [offset] of the byte-laid-out union whose base is [base].
   */
  @Serializable
  @SerialName("byteUnionValue")
  data class ByteUnionValue(val base: Expr<*>, val offset: Expr<*>, val widthBytes: Int) :
    StorageOrigin

  /**
   * An array member at byte [offset] of the byte-laid-out union whose base is [base], not yet
   * subscripted: `[i]` resolves to the bytes at `offset + i * elementBytes`.
   */
  @Serializable
  @SerialName("byteUnionArray")
  data class ByteUnionArray(val base: Expr<*>, val offset: Expr<*>, val elementBytes: Int) :
    StorageOrigin

  /**
   * A nested struct or union member at byte [offset] of the byte-laid-out union whose base is
   * [base], not yet accessed further: `.field` resolves to a byte slice at `offset` plus the
   * field's own offset.
   */
  @Serializable
  @SerialName("byteUnionStruct")
  data class ByteUnionStruct(val base: Expr<*>, val offset: Expr<*>) : StorageOrigin
}
