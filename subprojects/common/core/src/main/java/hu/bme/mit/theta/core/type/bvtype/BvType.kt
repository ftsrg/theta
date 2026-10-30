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
package hu.bme.mit.theta.core.type.bvtype

import com.google.common.base.Preconditions.checkArgument
import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.serialization.TypeReferenceSerializer
import hu.bme.mit.theta.core.type.AddExpr
import hu.bme.mit.theta.core.type.BvEqExpr
import hu.bme.mit.theta.core.type.BvNeqExpr
import hu.bme.mit.theta.core.type.DivExpr
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.EqExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.GeqExpr
import hu.bme.mit.theta.core.type.GtExpr
import hu.bme.mit.theta.core.type.LeqExpr
import hu.bme.mit.theta.core.type.LtExpr
import hu.bme.mit.theta.core.type.ModExpr
import hu.bme.mit.theta.core.type.MulExpr
import hu.bme.mit.theta.core.type.NegExpr
import hu.bme.mit.theta.core.type.NeqExpr
import hu.bme.mit.theta.core.type.PosExpr
import hu.bme.mit.theta.core.type.RemExpr
import hu.bme.mit.theta.core.type.SubExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.Additive
import hu.bme.mit.theta.core.type.abstracttype.Castable
import hu.bme.mit.theta.core.type.abstracttype.Divisible
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative
import hu.bme.mit.theta.core.type.abstracttype.Ordered
import hu.bme.mit.theta.core.type.bvtype.BvExprs.ToInt
import hu.bme.mit.theta.core.type.fptype.FpExprs.FromBv
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntType
import java.math.BigInteger
import kotlinx.serialization.KeepGeneratedSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

/**
 * A bitvector type of [size] bits. [signedness] is `null` for a "neutral" bitvector, which carries
 * no signedness at all and cannot be compared (see [Lt]); equality ignores it.
 */
@Serializable(with = TypeReferenceSerializer::class)
@KeepGeneratedSerializer
@SerialName("bv")
class BvType private constructor(val size: Int, val signedness: Boolean?) :
  Additive<BvType>,
  Multiplicative<BvType>,
  Divisible<BvType>,
  Equational<BvType>,
  Ordered<BvType>,
  Castable<BvType> {

  init {
    checkArgument(size > 0)
  }

  @Transient @Volatile private var hashCode = 0

  /** Whether this is a signed bitvector; a neutral one counts as unsigned. */
  val signed: Boolean
    get() = signedness == true

  fun withSize(size: Int): BvType = BvType(size, signedness)

  override fun Eq(leftOp: Expr<BvType>, rightOp: Expr<BvType>): EqExpr<BvType> =
    BvEqExpr.of(leftOp, rightOp)

  override fun Neq(leftOp: Expr<BvType>, rightOp: Expr<BvType>): NeqExpr<BvType> =
    BvNeqExpr.of(leftOp, rightOp)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + size
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    this === other ||
      (other != null && javaClass == other.javaClass && size == (other as BvType).size)

  override fun toString(): String = Utils.lispStringBuilder(TYPE_LABEL).add(size).toString()

  override fun Add(ops: Iterable<Expr<BvType>>): AddExpr<BvType> = BvExprs.Add(ops)

  override fun Sub(leftOp: Expr<BvType>, rightOp: Expr<BvType>): SubExpr<BvType> =
    BvExprs.Sub(leftOp, rightOp)

  override fun Pos(op: Expr<BvType>): PosExpr<BvType> = BvExprs.Pos(op)

  override fun Neg(op: Expr<BvType>): NegExpr<BvType> = BvExprs.Neg(op)

  @Suppress("UNCHECKED_CAST")
  override fun <TargetType : Type> Cast(op: Expr<BvType>, type: TargetType): Expr<TargetType> =
    if (type is FpType && signedness != null) {
      FromBv(FpRoundingMode.getDefaultRoundingMode(), op, type, signedness) as Expr<TargetType>
    } else if (type is IntType) {
      ToInt(op) as Expr<TargetType>
    } else {
      throw ClassCastException("Bv cannot be cast to $type")
    }

  override fun Mod(leftOp: Expr<BvType>, rightOp: Expr<BvType>): ModExpr<BvType> {
    checkState(signedness != null, "Neutral BvType cannot be used here")
    checkState(signedness!!, "Unsigned BvType cannot be used here")
    return BvExprs.SMod(leftOp, rightOp)
  }

  override fun Rem(leftOp: Expr<BvType>, rightOp: Expr<BvType>): RemExpr<BvType> =
    if (signedOrThrow()) BvExprs.SRem(leftOp, rightOp) else BvExprs.URem(leftOp, rightOp)

  override fun Mul(ops: Iterable<Expr<BvType>>): MulExpr<BvType> = BvExprs.Mul(ops)

  override fun Div(leftOp: Expr<BvType>, rightOp: Expr<BvType>): DivExpr<BvType> =
    if (signedOrThrow()) BvExprs.SDiv(leftOp, rightOp) else BvExprs.UDiv(leftOp, rightOp)

  override fun Lt(leftOp: Expr<BvType>, rightOp: Expr<BvType>): LtExpr<BvType> =
    if (signedOrThrow()) BvExprs.SLt(leftOp, rightOp) else BvExprs.ULt(leftOp, rightOp)

  override fun Leq(leftOp: Expr<BvType>, rightOp: Expr<BvType>): LeqExpr<BvType> =
    if (signedOrThrow()) BvExprs.SLeq(leftOp, rightOp) else BvExprs.ULeq(leftOp, rightOp)

  override fun Gt(leftOp: Expr<BvType>, rightOp: Expr<BvType>): GtExpr<BvType> =
    if (signedOrThrow()) BvExprs.SGt(leftOp, rightOp) else BvExprs.UGt(leftOp, rightOp)

  override fun Geq(leftOp: Expr<BvType>, rightOp: Expr<BvType>): GeqExpr<BvType> =
    if (signedOrThrow()) BvExprs.SGeq(leftOp, rightOp) else BvExprs.UGeq(leftOp, rightOp)

  override val domainSize: DomainSize
    get() = DomainSize.of(BigInteger.TWO.pow(size))

  private fun signedOrThrow(): Boolean {
    checkState(signedness != null, "Neutral BvType cannot be used here")
    return signedness!!
  }

  companion object {
    private const val HASH_SEED = 5674
    private const val TYPE_LABEL = "Bv"

    @JvmStatic fun of(size: Int): BvType = BvType(size, null)

    @JvmStatic fun of(size: Int, signed: Boolean?): BvType = BvType(size, signed)
  }
}
