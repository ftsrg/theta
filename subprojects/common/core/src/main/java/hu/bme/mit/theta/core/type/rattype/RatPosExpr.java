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

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.PosExpr;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class RatPosExpr extends PosExpr<RatType> {

	private static final int HASH_SEED = 4827;
	private static final String OPERATOR_LABEL = "+";

	private RatPosExpr(final Expr<RatType> op) {
		super(op);
	}

	public static RatPosExpr of(final Expr<RatType> op) {
		return new RatPosExpr(op);
	}

	public static RatPosExpr create(final Expr<?> op) {
		final Expr<RatType> newOp = cast(op, Rat());
		return RatPosExpr.of(newOp);
	}

	@Override
	public RatType getType() {
		return Rat();
	}

	@Override
	public RatLitExpr eval(final Valuation val) {
		final RatLitExpr opVal = (RatLitExpr) getOp().eval(val);
		return opVal.pos();
	}

	@Override
	public RatPosExpr with(final Expr<RatType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return RatPosExpr.of(op);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatPosExpr) {
			final RatPosExpr that = (RatPosExpr) obj;
			return this.getOp().equals(that.getOp());
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
