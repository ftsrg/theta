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
package hu.bme.mit.theta.core.type.rattype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import java.math.BigInteger
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("RatAdd")
class RatAddExpr(override val ops: List<Expr<RatType>>) : AddExpr<RatType>() {

  companion object {

    private const val OPERATOR_LABEL = "+"

    @JvmStatic fun of(ops: Iterable<Expr<RatType>>): RatAddExpr = RatAddExpr(ops.toList())

    @Suppress("UNCHECKED_CAST")
    @JvmStatic
    fun create(ops: Iterable<Expr<*>>): RatAddExpr = RatAddExpr(ops.map { it as Expr<RatType> })
  }

  override val type: RatType = Rat()

  override fun eval(`val`: Valuation): RatLitExpr {
    var sumNum = BigInteger.ZERO
    var sumDenom = BigInteger.ONE
    ops.forEach { op ->
      val opLit = op.eval(`val`) as RatLitExpr
      val leftNum = sumNum
      val leftDenom = sumDenom
      val rightNum = opLit.num
      val rightDenom = opLit.denom
      sumNum = leftNum.multiply(rightDenom).add(leftDenom.multiply(rightNum))
      sumDenom = leftDenom.multiply(rightDenom)
    }
    return Rat(sumNum, sumDenom)
  }

  override fun new(ops: List<Expr<RatType>>): RatAddExpr = new(ops)

  override val operatorLabel: String = OPERATOR_LABEL

  override fun toString(): String = super.toString()
}
