/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.GtExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public final class BvUGtExpr extends GtExpr<BvType> {

	private static final int HASH_SEED = 6231;
	private static final String OPERATOR_LABEL = "bvugt";

	private BvUGtExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
		super(leftOp, rightOp);
		checkAllTypesEqual(leftOp, rightOp);
	}

	public static BvUGtExpr of(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
		return new BvUGtExpr(leftOp, rightOp);
	}

	public static BvUGtExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Expr<BvType> newLeftOp = castBv(leftOp);
		final Expr<BvType> newRightOp = castBv(rightOp);
		return BvUGtExpr.of(newLeftOp, newRightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public LitExpr<BoolType> eval(final Valuation val) {
		final BvLitExpr leftOpVal = (BvLitExpr) getLeftOp().eval(val);
		final BvLitExpr rightOpVal = (BvLitExpr) getRightOp().eval(val);
		return leftOpVal.ugt(rightOpVal);
	}

	@Override
	public BvUGtExpr with(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return BvUGtExpr.of(leftOp, rightOp);
		}
	}

	@Override
	public BvUGtExpr withLeftOp(final Expr<BvType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public BvUGtExpr withRightOp(final Expr<BvType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof BvUGtExpr) {
			final BvUGtExpr that = (BvUGtExpr) obj;
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
