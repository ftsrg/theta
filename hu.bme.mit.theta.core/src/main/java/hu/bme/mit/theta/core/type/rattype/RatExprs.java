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

public final class RatExprs {

	private RatExprs() {
	}

	public static RatType Rat() {
		return RatType.getInstance();
	}

	public static RatLitExpr Rat(final int num, final int denom) {
		return new RatLitExpr(num, denom);
	}

	public static RatAddExpr Add(final Iterable<? extends Expr<RatType>> ops) {
		return new RatAddExpr(ops);
	}

	public static RatSubExpr Sub(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatSubExpr(leftOp, rightOp);
	}

	public static RatNegExpr Neg(final Expr<RatType> op) {
		return new RatNegExpr(op);
	}

	public static RatMulExpr Mul(final Iterable<? extends Expr<RatType>> ops) {
		return new RatMulExpr(ops);
	}

	public static RatDivExpr Div(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatDivExpr(leftOp, rightOp);
	}

	public static RatEqExpr Eq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatEqExpr(leftOp, rightOp);
	}

	public static RatNeqExpr Neq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatNeqExpr(leftOp, rightOp);
	}

	public static RatLtExpr Lt(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatLtExpr(leftOp, rightOp);
	}

	public static RatLeqExpr Leq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatLeqExpr(leftOp, rightOp);
	}

	public static RatGtExpr Gt(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatGtExpr(leftOp, rightOp);
	}

	public static RatGeqExpr Geq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatGeqExpr(leftOp, rightOp);
	}

	/*
	 * Convenience methods
	 */

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2) {
		return Add(ImmutableList.of(op1, op2));
	}

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3) {
		return Add(ImmutableList.of(op1, op2, op3));
	}

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
			final Expr<RatType> op4) {
		return Add(ImmutableList.of(op1, op2, op3, op4));
	}

	public static RatAddExpr Add(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
			final Expr<RatType> op4, final Expr<RatType> op5) {
		return Add(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2) {
		return Mul(ImmutableList.of(op1, op2));
	}

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3) {
		return Mul(ImmutableList.of(op1, op2, op3));
	}

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
			final Expr<RatType> op4) {
		return Mul(ImmutableList.of(op1, op2, op3, op4));
	}

	public static RatMulExpr Mul(final Expr<RatType> op1, final Expr<RatType> op2, final Expr<RatType> op3,
			final Expr<RatType> op4, final Expr<RatType> op5) {
		return Mul(ImmutableList.of(op1, op2, op3, op4, op5));
	}

}
