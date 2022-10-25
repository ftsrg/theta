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
import hu.bme.mit.theta.core.type.abstracttype.PosExpr;

import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;

public final class BvPosExpr extends PosExpr<BvType> {

	private static final int HASH_SEED = 8962;
	private static final String OPERATOR_LABEL = "bvpos";

	private BvPosExpr(final Expr<BvType> op) {
		super(op);
	}

	public static BvPosExpr of(final Expr<BvType> op) {
		return new BvPosExpr(op);
	}

	public static BvPosExpr create(final Expr<?> op) {
		final Expr<BvType> newOp = castBv(op);
		return BvPosExpr.of(newOp);
	}

	@Override
	public BvType getType() {
		return getOp().getType();
	}

	@Override
	public BvLitExpr eval(final Valuation val) {
		final BvLitExpr opVal = (BvLitExpr) getOp().eval(val);
		return opVal.pos();
	}

	@Override
	public BvPosExpr with(final Expr<BvType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return BvPosExpr.of(op);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof BvPosExpr) {
			final BvPosExpr that = (BvPosExpr) obj;
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
