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
package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.utils.FpUtils;
import org.kframework.mpfr.BigFloat;

import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public final class FpRemExpr extends BinaryExpr<FpType, FpType> {

	private static final int HASH_SEED = 6670;

	private static final String OPERATOR_LABEL = "fprem";

	private FpRemExpr(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		super(leftOp, rightOp);
		checkAllTypesEqual(leftOp, rightOp);
	}

	public static FpRemExpr of(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return new FpRemExpr(leftOp, rightOp);
	}

	public static FpRemExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Expr<FpType> newLeftOp = castFp(leftOp);
		final Expr<FpType> newRightOp = castFp(rightOp);
		return FpRemExpr.of(newLeftOp, newRightOp);
	}

	@Override
	public FpType getType() {
		return getLeftOp().getType();
	}

	@Override
	public FpLitExpr eval(final Valuation val) {
		final FpLitExpr leftOpVal = (FpLitExpr) getLeftOp().eval(val);
		final FpLitExpr rightOpVal = (FpLitExpr) getRightOp().eval(val);
		BigFloat leftFloat = FpUtils.fpLitExprToBigFloat(null, leftOpVal);
		BigFloat rightFloat = FpUtils.fpLitExprToBigFloat(null, rightOpVal);
		BigFloat remainder = leftFloat.remainder(rightFloat, FpUtils.getMathContext(this.getType(), null));

		return FpUtils.bigFloatToFpLitExpr(remainder, this.getType());
	}

	@Override


	public FpRemExpr with(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return FpRemExpr.of(leftOp, rightOp);
		}
	}

	@Override
	public FpRemExpr withLeftOp(final Expr<FpType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public FpRemExpr withRightOp(final Expr<FpType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FpRemExpr) {
			final FpRemExpr that = (FpRemExpr) obj;
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
 
