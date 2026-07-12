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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.DivExpr
import hu.bme.mit.theta.core.type.abstracttype.MulExpr
import hu.bme.mit.theta.core.type.abstracttype.NegExpr
import hu.bme.mit.theta.core.type.abstracttype.SubExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.utils.BvUtils
import java.math.BigInteger

/**
 * Whether a signed bitvector operation overflows.
 *
 * Under integer arithmetic an operation is carried out in the unbounded integers, so overflow is
 * detected by simply range-checking the result against the C type's limits. A bitvector operation
 * gives no such handle: it has *already* wrapped, so the result is trivially in range, and SMT-LIB
 * has no overflow flag to consult. (Z3 does expose `bvadd_no_overflow` and friends, but they are
 * non-standard, so relying on them would tie overflow checking to one solver.)
 *
 * The portable encoding is to **redo the operation in a wider bitvector and see whether the narrow
 * result still agrees**: `a + b` overflows exactly when sign-extending the wrapped w-bit sum does
 * not give the same value as adding the sign-extended operands in w+1 bits. One extra bit suffices
 * for addition and subtraction; a product needs 2w. Negation and division cannot be caught this way
 * -- they each overflow on exactly one input -- so they are stated directly.
 *
 * C evaluates `a + b + c` as `(a + b) + c`, and either step can overflow on its own, so an n-ary
 * operation is folded left to right and each step is checked against the *wrapped* running value,
 * exactly as the program computes it.
 */
fun bvOverflowCondition(expr: Expr<*>): Expr<BoolType>? {
  val type = expr.type as? BvType ?: return null
  val width = type.size

  @Suppress("UNCHECKED_CAST") fun bv(e: Expr<*>): Expr<BvType> = e as Expr<BvType>

  fun widen(e: Expr<BvType>, to: Int): Expr<BvType> = BvExprs.SExt(e, BvType.of(to, true))

  fun lit(value: BigInteger): Expr<BvType> = BvUtils.bigIntegerToSignedBvLitExpr(value, width)

  /** The op disagrees with itself carried out in `wide` bits: that is exactly an overflow. */
  fun disagrees(narrow: Expr<BvType>, wide: Int, inWide: (Int) -> Expr<BvType>): Expr<BoolType> =
    Not(Eq(widen(narrow, wide), inWide(wide)))

  fun foldChecks(
    ops: List<Expr<BvType>>,
    wide: Int,
    step: (Expr<BvType>, Expr<BvType>) -> Expr<BvType>,
  ): Expr<BoolType> {
    val checks = mutableListOf<Expr<BoolType>>()
    var acc = ops[0]
    for (op in ops.drop(1)) {
      val next = step(acc, op)
      val a = acc
      checks.add(disagrees(next, wide) { w -> step(widen(a, w), widen(op, w)) })
      acc = next // the program carries on with the wrapped value, so we must too
    }
    return if (checks.size == 1) checks[0] else Or(checks)
  }

  return when (expr) {
    is AddExpr<*> -> foldChecks(expr.ops.map(::bv), width + 1) { a, b -> BvExprs.Add(listOf(a, b)) }

    is SubExpr<*> -> {
      val a = bv(expr.leftOp)
      val b = bv(expr.rightOp)
      disagrees(BvExprs.Sub(a, b), width + 1) { w -> BvExprs.Sub(widen(a, w), widen(b, w)) }
    }

    is MulExpr<*> -> foldChecks(expr.ops.map(::bv), width * 2) { a, b -> BvExprs.Mul(listOf(a, b)) }

    // -x overflows on exactly one value: the most negative one, which has no positive counterpart.
    is NegExpr<*> -> Eq(bv(expr.op), lit(BigInteger.TWO.pow(width - 1).negate()))

    // `a << b` is `a * 2^b`, so it overflows when that product no longer fits -- redone in twice
    // the
    // width, the shifted value must still agree with the narrow one. (A *negative* `a` is undefined
    // in C regardless, but flagging that would condemn the common `-1 << k` idiom, so only the
    // value
    // is checked.)
    is BvShiftLeftExpr -> {
      val a = bv(expr.leftOp)
      val b = bv(expr.rightOp)
      disagrees(BvExprs.ShiftLeft(a, b), width * 2) { w ->
        BvExprs.ShiftLeft(widen(a, w), widen(b, w))
      }
    }

    // Likewise x / y: only MIN / -1 overflows (its true value is one past MAX).
    is DivExpr<*> ->
      And(
        Eq(bv(expr.leftOp), lit(BigInteger.TWO.pow(width - 1).negate())),
        Eq(bv(expr.rightOp), lit(BigInteger.ONE.negate())),
      )

    else -> null
  }
}
