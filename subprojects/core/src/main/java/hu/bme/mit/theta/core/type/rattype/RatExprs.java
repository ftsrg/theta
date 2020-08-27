/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.type.rattype;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.type.Expr;

import java.math.BigInteger;

public final class RatExprs {

	private RatExprs() {
	}

	public static RatType Rat() {
		return RatType.getInstance();
	}

	public static RatLitExpr Rat(final int num, final int denom) {
		return RatLitExpr.of(BigInteger.valueOf(num), BigInteger.valueOf(denom));
	}

	public static RatLitExpr Rat(final int num, final String denom) {
		return RatLitExpr.of(BigInteger.valueOf(num), new BigInteger(denom));
	}

	public static RatLitExpr Rat(final int num, final BigInteger denom) {
		return RatLitExpr.of(BigInteger.valueOf(num), denom);
	}

	public static RatLitExpr Rat(final String num, final int denom) {
		return RatLitExpr.of(new BigInteger(num), BigInteger.valueOf(denom));
	}

	public static RatLitExpr Rat(final String num, final String denom) {
		return RatLitExpr.of(new BigInteger(num), new BigInteger(denom));
	}

	public static RatLitExpr Rat(final String num, final BigInteger denom) {
		return RatLitExpr.of(new BigInteger(num), denom);
	}

	public static RatLitExpr Rat(final BigInteger num, final int denom) {
		return RatLitExpr.of(num, BigInteger.valueOf(denom));
	}

	public static RatLitExpr Rat(final BigInteger num, final String denom) {
		return RatLitExpr.of(num, new BigInteger(denom));
	}

	public static RatLitExpr Rat(final BigInteger num, final BigInteger denom) {
		return RatLitExpr.of(num, denom);
	}

	public static RatAddExpr Add(final Iterable<? extends Expr<RatType>> ops) {
		return RatAddExpr.of(ops);
	}

	public static RatSubExpr Sub(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatSubExpr.of(leftOp, rightOp);
	}

	public static RatPosExpr Pos(final Expr<RatType> op) {
		return RatPosExpr.of(op);
	}

	public static RatNegExpr Neg(final Expr<RatType> op) {
		return RatNegExpr.of(op);
	}

	public static RatMulExpr Mul(final Iterable<? extends Expr<RatType>> ops) {
		return RatMulExpr.of(ops);
	}

	public static RatDivExpr Div(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatDivExpr.of(leftOp, rightOp);
	}

	public static RatEqExpr Eq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatEqExpr.of(leftOp, rightOp);
	}

	public static RatNeqExpr Neq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatNeqExpr.of(leftOp, rightOp);
	}

	public static RatLtExpr Lt(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatLtExpr.of(leftOp, rightOp);
	}

	public static RatLeqExpr Leq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatLeqExpr.of(leftOp, rightOp);
	}

	public static RatGtExpr Gt(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatGtExpr.of(leftOp, rightOp);
	}

	public static RatGeqExpr Geq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatGeqExpr.of(leftOp, rightOp);
	}

	/*
	 * Convenience methods
	 */

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2) {
		return RatAddExpr.of(ImmutableList.of(op1, op2));
	}

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3) {
		return RatAddExpr.of(ImmutableList.of(op1, op2, op3));
	}

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
								 final Expr<RatType> op4) {
		return RatAddExpr.of(ImmutableList.of(op1, op2, op3, op4));
	}

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
								 final Expr<RatType> op4, final Expr<RatType> op5) {
		return RatAddExpr.of(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2) {
		return RatMulExpr.of(ImmutableList.of(op1, op2));
	}

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3) {
		return RatMulExpr.of(ImmutableList.of(op1, op2, op3));
	}

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
								 final Expr<RatType> op4) {
		return RatMulExpr.of(ImmutableList.of(op1, op2, op3, op4));
	}

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
								 final Expr<RatType> op4, final Expr<RatType> op5) {
		return RatMulExpr.of(ImmutableList.of(op1, op2, op3, op4, op5));
	}

}
