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
import hu.bme.mit.theta.core.type.abstracttype.RemExpr;

import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public final class BvSRemExpr extends RemExpr<BvType> {

	private static final int HASH_SEED = 985;

	private static final String OPERATOR_LABEL = "bvsrem";

	private BvSRemExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
		super(leftOp, rightOp);
		checkAllTypesEqual(leftOp, rightOp);
	}

	public static BvSRemExpr of(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
		return new BvSRemExpr(leftOp, rightOp);
	}

	public static BvSRemExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Expr<BvType> newLeftOp = castBv(leftOp);
		final Expr<BvType> newRightOp = castBv(rightOp);
		return BvSRemExpr.of(newLeftOp, newRightOp);
	}

	@Override
	public BvType getType() {
		return getOps().get(0).getType();
	}

	@Override
	public BvLitExpr eval(final Valuation val) {
		final BvLitExpr leftOpVal = (BvLitExpr) getLeftOp().eval(val);
		final BvLitExpr rightOpVal = (BvLitExpr) getRightOp().eval(val);
		return leftOpVal.srem(rightOpVal);
	}

	@Override
	public BvSRemExpr with(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return BvSRemExpr.of(leftOp, rightOp);
		}
	}

	@Override
	public BvSRemExpr withLeftOp(final Expr<BvType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public BvSRemExpr withRightOp(final Expr<BvType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof BvSRemExpr) {
			final BvSRemExpr that = (BvSRemExpr) obj;
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
