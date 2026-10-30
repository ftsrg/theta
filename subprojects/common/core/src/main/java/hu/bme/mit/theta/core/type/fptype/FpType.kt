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
package hu.bme.mit.theta.core.type.fptype

import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.serialization.TypeReferenceSerializer
import hu.bme.mit.theta.core.type.AddExpr
import hu.bme.mit.theta.core.type.DivExpr
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.EqExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.FpEqExpr
import hu.bme.mit.theta.core.type.FpNeqExpr
import hu.bme.mit.theta.core.type.GeqExpr
import hu.bme.mit.theta.core.type.GtExpr
import hu.bme.mit.theta.core.type.LeqExpr
import hu.bme.mit.theta.core.type.LtExpr
import hu.bme.mit.theta.core.type.MulExpr
import hu.bme.mit.theta.core.type.NegExpr
import hu.bme.mit.theta.core.type.NeqExpr
import hu.bme.mit.theta.core.type.PosExpr
import hu.bme.mit.theta.core.type.SubExpr
import hu.bme.mit.theta.core.type.abstracttype.Additive
import hu.bme.mit.theta.core.type.abstracttype.Equational
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative
import hu.bme.mit.theta.core.type.abstracttype.Ordered
import java.math.BigInteger
import kotlinx.serialization.KeepGeneratedSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

@Serializable(with = TypeReferenceSerializer::class)
@KeepGeneratedSerializer
@SerialName("fp")
class FpType private constructor(val exponent: Int, val significand: Int) :
  Equational<FpType>, Additive<FpType>, Multiplicative<FpType>, Ordered<FpType> {

  init {
    checkArgument(exponent > 1)
    checkArgument(significand > 1)
  }

  @Transient @Volatile private var hashCode = 0

  override fun Eq(leftOp: Expr<FpType>, rightOp: Expr<FpType>): EqExpr<FpType> =
    FpEqExpr.of(leftOp, rightOp)

  override fun Neq(leftOp: Expr<FpType>, rightOp: Expr<FpType>): NeqExpr<FpType> =
    FpNeqExpr.of(leftOp, rightOp)

  override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + exponent
      result = 31 * result + significand
      hashCode = result
    }
    return result
  }

  override fun equals(other: Any?): Boolean =
    this === other ||
      (other != null &&
        javaClass == other.javaClass &&
        exponent == (other as FpType).exponent &&
        significand == other.significand)

  override fun toString(): String =
    Utils.lispStringBuilder(TYPE_LABEL).add(exponent).add(significand).toString()

  override fun Add(ops: Iterable<Expr<FpType>>): AddExpr<FpType> =
    FpExprs.Add(FpRoundingMode.getDefaultRoundingMode(), ops)

  override fun Sub(leftOp: Expr<FpType>, rightOp: Expr<FpType>): SubExpr<FpType> =
    FpExprs.Sub(FpRoundingMode.getDefaultRoundingMode(), leftOp, rightOp)

  override fun Pos(op: Expr<FpType>): PosExpr<FpType> = FpExprs.Pos(op)

  override fun Neg(op: Expr<FpType>): NegExpr<FpType> = FpExprs.Neg(op)

  override fun Mul(ops: Iterable<Expr<FpType>>): MulExpr<FpType> =
    FpExprs.Mul(FpRoundingMode.getDefaultRoundingMode(), ops)

  override fun Div(leftOp: Expr<FpType>, rightOp: Expr<FpType>): DivExpr<FpType> =
    FpExprs.Div(FpRoundingMode.getDefaultRoundingMode(), leftOp, rightOp)

  override fun Lt(leftOp: Expr<FpType>, rightOp: Expr<FpType>): LtExpr<FpType> =
    FpExprs.Lt(leftOp, rightOp)

  override fun Leq(leftOp: Expr<FpType>, rightOp: Expr<FpType>): LeqExpr<FpType> =
    FpExprs.Leq(leftOp, rightOp)

  override fun Gt(leftOp: Expr<FpType>, rightOp: Expr<FpType>): GtExpr<FpType> =
    FpExprs.Gt(leftOp, rightOp)

  override fun Geq(leftOp: Expr<FpType>, rightOp: Expr<FpType>): GeqExpr<FpType> =
    FpExprs.Geq(leftOp, rightOp)

  override val domainSize: DomainSize
    get() = DomainSize.of(BigInteger.TWO.pow(significand).multiply(BigInteger.TWO.pow(exponent)))

  companion object {
    private const val HASH_SEED = 5424
    private const val TYPE_LABEL = "Fp"

    @JvmStatic fun of(exponent: Int, significand: Int): FpType = FpType(exponent, significand)
  }
}
