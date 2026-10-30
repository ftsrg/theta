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
package hu.bme.mit.theta.frontend.transformation.model.statements

import com.google.common.base.Preconditions.checkNotNull
import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType

class CAssignment(
  private val lValue: Expr<*>,
  private val rValue: CStatement,
  val operator: String,
  parseContext: ParseContext,
) : CStatement(parseContext) {

  init {
    checkNotNull(rValue.expression)
    rValue.setParent(this)
  }

  fun getrValue(): CStatement = rValue

  fun getlValue(): Expr<*> = lValue

  override val expression: Expr<*>
    get() = lValue

  override fun <P, R> accept(visitor: CStatementVisitor<P, R>, param: P): R =
    visitor.visit(this, param)

  private fun checkBitvectors(op: String, rExpression: Expr<*>, kind: String) =
    checkState(
      lValue.type is BvType && rExpression.type is BvType,
      "The compound $kind assignment `%s` is only modelled over bitvectors, but the operands have" +
        " types %s and %s. This is expected under --arithmetic integer, which has no bit" +
        " representation; use --arithmetic bitvector or efficient.",
      op,
      lValue.type,
      rExpression.type,
    )

  @Suppress("UNCHECKED_CAST")
  fun getrExpression(): Expr<*> {
    // Non-null: checked when the assignment was built.
    val rExpression = rValue.expression!!
    val type = CComplexType.getType(lValue, parseContext)
    var ret: Expr<*> =
      when (operator) {
        "=" -> return rExpression
        "*=" -> AbstractExprs.Mul(type.castTo(lValue), type.castTo(rExpression))
        "/=" -> AbstractExprs.Div(type.castTo(lValue), type.castTo(rExpression))
        "%=" -> {
          // C's `%` is truncated remainder, not floored modulo: `Rem` (URem/SRem by signedness)
          // for bitvectors, matching the binary `%` operator. `Mod` mapped to the signed-only SMod
          // and threw ("Unsigned BvType cannot be used here") on an unsigned `x %= y`.
          val modLeft = type.castTo(lValue)
          val modRight = type.castTo(rExpression)
          if (modLeft.type is BvType && modRight.type is BvType)
            AbstractExprs.Rem(modLeft, modRight)
          else AbstractExprs.Mod(modLeft, modRight)
        }
        "+=" -> AbstractExprs.Add(type.castTo(lValue), type.castTo(rExpression))
        "-=" -> AbstractExprs.Sub(type.castTo(lValue), type.castTo(rExpression))
        "^=" -> {
          checkBitvectors("^=", rExpression, "bitwise")
          BvExprs.Xor(
            listOf(type.castTo(lValue) as Expr<BvType>, type.castTo(rExpression) as Expr<BvType>)
          )
        }
        "&=" -> {
          checkBitvectors("&=", rExpression, "bitwise")
          BvExprs.And(
            listOf(type.castTo(lValue) as Expr<BvType>, type.castTo(rExpression) as Expr<BvType>)
          )
        }
        "|=" -> {
          checkBitvectors("|=", rExpression, "bitwise")
          BvExprs.Or(
            listOf(type.castTo(lValue) as Expr<BvType>, type.castTo(rExpression) as Expr<BvType>)
          )
        }
        ">>=" -> {
          checkBitvectors(">>=", rExpression, "shift")
          val left = type.castTo(lValue) as Expr<BvType>
          val right = type.castTo(rExpression) as Expr<BvType>
          // Right shift is arithmetic on a signed left operand and logical on an unsigned one --
          // the same split `visitShiftExpression` makes for the non-assigning `>>`.
          if (left.type.signed) BvExprs.ArithShiftRight(left, right)
          else BvExprs.LogicShiftRight(left, right)
        }
        "<<=" -> {
          checkBitvectors("<<=", rExpression, "shift")
          BvExprs.ShiftLeft(
            type.castTo(lValue) as Expr<BvType>,
            type.castTo(rExpression) as Expr<BvType>,
          )
        }
        else -> throw UnsupportedFrontendElementException("Unsupported operator: $operator")
      }
    ret = CComplexType.withType(ret, CComplexType.getType(lValue, parseContext))
    ret = CComplexType.getType(lValue, parseContext).castTo(ret)
    ret = CComplexType.withType(ret, CComplexType.getType(lValue, parseContext))
    return ret
  }
}
