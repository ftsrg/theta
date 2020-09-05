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
package hu.bme.mit.theta.core.type.booltype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;

public final class XorExpr extends NeqExpr<BoolType> {

	private static final int HASH_SEED = 937;

	private static final String OPERATOR_LABEL = "xor";

	private XorExpr(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		super(leftOp, rightOp);
	}

	public static XorExpr of(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		return new XorExpr(leftOp, rightOp);
	}

	public static XorExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Expr<BoolType> newLeftOp = cast(leftOp, Bool());
		final Expr<BoolType> newRightOp = cast(rightOp, Bool());
		return XorExpr.of(newLeftOp, newRightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public LitExpr<BoolType> eval(final Valuation val) {
		final BoolLitExpr leftOpVal = (BoolLitExpr) getLeftOp().eval(val);
		final BoolLitExpr rightOpVal = (BoolLitExpr) getRightOp().eval(val);
		return Bool(leftOpVal.getValue() != rightOpVal.getValue());
	}

	@Override
	public BinaryExpr<BoolType, BoolType> with(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return XorExpr.of(leftOp, rightOp);
		}
	}

	@Override
	public BinaryExpr<BoolType, BoolType> withLeftOp(final Expr<BoolType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public BinaryExpr<BoolType, BoolType> withRightOp(final Expr<BoolType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof XorExpr) {
			final XorExpr that = (XorExpr) obj;
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
