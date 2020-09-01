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

import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import java.math.BigInteger;
import java.util.List;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;

public final class RatMulExpr extends MulExpr<RatType> {

	private static final int HASH_SEED = 9479;
	private static final String OPERATOR_LABEL = "*";

	private RatMulExpr(final Iterable<? extends Expr<RatType>> ops) {
		super(ops);
	}

	public static RatMulExpr of(final Iterable<? extends Expr<RatType>> ops) {
		return new RatMulExpr(ops);
	}

	public static RatMulExpr create(final List<? extends Expr<?>> ops) {
		return RatMulExpr.of(ops.stream().map(op -> cast(op, Rat())).collect(toImmutableList()));
	}

	@Override
	public RatType getType() {
		return Rat();
	}

	@Override
	public RatLitExpr eval(final Valuation val) {
		var prodNum = BigInteger.ONE;
		var prodDenom = BigInteger.ONE;
		for (final Expr<RatType> op : getOps()) {
			final RatLitExpr opLit = (RatLitExpr) op.eval(val);
			prodNum = prodNum.multiply(opLit.getNum());
			prodDenom = prodDenom.multiply(opLit.getDenom());
		}
		return Rat(prodNum, prodDenom);
	}

	@Override
	public RatMulExpr with(final Iterable<? extends Expr<RatType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new RatMulExpr(ops);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatMulExpr) {
			final RatMulExpr that = (RatMulExpr) obj;
			return this.getOps().equals(that.getOps());
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
