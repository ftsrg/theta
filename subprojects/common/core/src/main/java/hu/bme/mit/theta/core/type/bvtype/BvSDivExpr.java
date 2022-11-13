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
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;

import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public final class BvSDivExpr extends DivExpr<BvType> {
	private static final int HASH_SEED = 9830;

	private static final String OPERATOR_LABEL = "bvsdiv";

	private BvSDivExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
		super(leftOp, rightOp);
		checkAllTypesEqual(leftOp, rightOp);
	}

	public static BvSDivExpr of(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
		return new BvSDivExpr(leftOp, rightOp);
	}

	public static BvSDivExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Expr<BvType> newLeftOp = castBv(leftOp);
		final Expr<BvType> newRightOp = castBv(rightOp);
		return BvSDivExpr.of(newLeftOp, newRightOp);
	}

	@Override
	public BvType getType() {
		return getOps().get(0).getType();
	}

	@Override
	public BvLitExpr eval(final Valuation val) {
		final BvLitExpr leftOpVal = (BvLitExpr) getLeftOp().eval(val);
		final BvLitExpr rightOpVal = (BvLitExpr) getRightOp().eval(val);

		return leftOpVal.sdiv(rightOpVal);
	}

	@Override
	public BvSDivExpr with(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return BvSDivExpr.of(leftOp, rightOp);
		}
	}

	@Override
	public BvSDivExpr withLeftOp(final Expr<BvType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public BvSDivExpr withRightOp(final Expr<BvType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof BvSDivExpr) {
			final BvSDivExpr that = (BvSDivExpr) obj;
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
