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

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;

public final class IntDivExpr extends DivExpr<IntType> {

	private static final int HASH_SEED = 79;

	private static final String OPERATOR_LABEL = "div";

	private IntDivExpr(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		super(leftOp, rightOp);
	}

	public static IntDivExpr of(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return new IntDivExpr(leftOp, rightOp);
	}

	public static IntDivExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Expr<IntType> newLeftOp = cast(leftOp, Int());
		final Expr<IntType> newRightOp = cast(rightOp, Int());
		return IntDivExpr.of(newLeftOp, newRightOp);
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntLitExpr eval(final Valuation val) {
		final IntLitExpr leftOpVal = (IntLitExpr) getLeftOp().eval(val);
		final IntLitExpr rightOpVal = (IntLitExpr) getRightOp().eval(val);
		return leftOpVal.div(rightOpVal);
	}

	@Override
	public IntDivExpr with(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return IntDivExpr.of(leftOp, rightOp);
		}
	}

	@Override
	public IntDivExpr withLeftOp(final Expr<IntType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public IntDivExpr withRightOp(final Expr<IntType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IntDivExpr) {
			final IntDivExpr that = (IntDivExpr) obj;
			return this.getLeftOp().equals(that.getLeftOp()) && this.getRightOp().equals(that.getRightOp());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
