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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class RatEqExpr extends EqExpr<RatType> {

	private static final int HASH_SEED = 3709;
	private static final String OPERATOR_LABEL = "=";

	private RatEqExpr(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		super(leftOp, rightOp);
	}

	public static RatEqExpr of(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return new RatEqExpr(leftOp, rightOp);
	}

	public static RatEqExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Expr<RatType> newLeftOp = cast(leftOp, Rat());
		final Expr<RatType> newRightOp = cast(rightOp, Rat());
		return RatEqExpr.of(newLeftOp, newRightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Valuation val) {
		final RatLitExpr leftOpVal = (RatLitExpr) getLeftOp().eval(val);
		final RatLitExpr rightOpVal = (RatLitExpr) getRightOp().eval(val);
		return leftOpVal.eq(rightOpVal);
	}

	@Override
	public RatEqExpr with(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return RatEqExpr.of(leftOp, rightOp);
		}
	}

	@Override
	public RatEqExpr withLeftOp(final Expr<RatType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public RatEqExpr withRightOp(final Expr<RatType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatEqExpr) {
			final RatEqExpr that = (RatEqExpr) obj;
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
