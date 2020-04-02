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
package hu.bme.mit.theta.core.type.inttype;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.type.Expr;

public final class IntExprs {

	private IntExprs() {
	}

	public static IntType Int() {
		return IntType.getInstance();
	}

	public static IntLitExpr Int(final int value) {
		return IntLitExpr.of(value);
	}

	public static IntToRatExpr ToRat(final Expr<IntType> op) {
		return IntToRatExpr.of(op);
	}

	public static IntToBvExpr ToBv(final Expr<IntType> op, final int size, final boolean isSigned) {
		return IntToBvExpr.of(op, size, isSigned);
	}

	public static IntAddExpr Add(final Iterable<? extends Expr<IntType>> ops) {
		return IntAddExpr.of(ops);
	}

	public static IntSubExpr Sub(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntSubExpr.of(leftOp, rightOp);
	}

	public static IntNegExpr Neg(final Expr<IntType> op) {
		return IntNegExpr.of(op);
	}

	public static IntMulExpr Mul(final Iterable<? extends Expr<IntType>> ops) {
		return IntMulExpr.of(ops);
	}

	public static IntDivExpr Div(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntDivExpr.of(leftOp, rightOp);
	}

	public static IntModExpr Mod(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntModExpr.of(leftOp, rightOp);
	}

	public static IntRemExpr Rem(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntRemExpr.of(leftOp, rightOp);
	}

	public static IntEqExpr Eq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntEqExpr.of(leftOp, rightOp);
	}

	public static IntNeqExpr Neq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntNeqExpr.of(leftOp, rightOp);
	}

	public static IntLtExpr Lt(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntLtExpr.of(leftOp, rightOp);
	}

	public static IntLeqExpr Leq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntLeqExpr.of(leftOp, rightOp);
	}

	public static IntGtExpr Gt(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntGtExpr.of(leftOp, rightOp);
	}

	public static IntGeqExpr Geq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntGeqExpr.of(leftOp, rightOp);
	}

	/*
	 * Convenience methods
	 */

	public static IntAddExpr Add(final Expr<IntType> op1, final Expr<IntType> op2) {
		return IntAddExpr.of(ImmutableList.of(op1, op2));
	}

	public static IntAddExpr Add(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3) {
		return IntAddExpr.of(ImmutableList.of(op1, op2, op3));
	}

	public static IntAddExpr Add(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3,
								 final Expr<IntType> op4) {
		return IntAddExpr.of(ImmutableList.of(op1, op2, op3, op4));
	}

	public static IntAddExpr Add(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3,
								 final Expr<IntType> op4, final Expr<IntType> op5) {
		return IntAddExpr.of(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static IntMulExpr Mul(final Expr<IntType> op1, final Expr<IntType> op2) {
		return IntMulExpr.of(ImmutableList.of(op1, op2));
	}

	public static IntMulExpr Mul(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3) {
		return IntMulExpr.of(ImmutableList.of(op1, op2, op3));
	}

	public static IntMulExpr Mul(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3,
								 final Expr<IntType> op4) {
		return IntMulExpr.of(ImmutableList.of(op1, op2, op3, op4));
	}

	public static IntMulExpr Mul(final Expr<IntType> op1, final Expr<IntType> op2, final Expr<IntType> op3,
								 final Expr<IntType> op4, final Expr<IntType> op5) {
		return IntMulExpr.of(ImmutableList.of(op1, op2, op3, op4, op5));
	}

}
