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

import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import java.math.BigInteger;
import java.util.List;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;

public final class IntMulExpr extends MulExpr<IntType> {

	private static final int HASH_SEED = 2707;
	private static final String OPERATOR_LABEL = "*";

	private IntMulExpr(final Iterable<? extends Expr<IntType>> ops) {
		super(ops);
	}

	public static IntMulExpr of(final Iterable<? extends Expr<IntType>> ops) {
		return new IntMulExpr(ops);
	}

	public static IntMulExpr create(final List<? extends Expr<?>> ops) {
		return IntMulExpr.of(ops.stream().map(op -> cast(op, Int())).collect(toImmutableList()));
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntLitExpr eval(final Valuation val) {
		var prod = BigInteger.ONE;
		for (final Expr<IntType> op : getOps()) {
			final IntLitExpr opVal = (IntLitExpr) op.eval(val);
			prod = prod.multiply(opVal.getValue());
		}
		return Int(prod);
	}

	@Override
	public IntMulExpr with(final Iterable<? extends Expr<IntType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return IntMulExpr.of(ops);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IntMulExpr) {
			final IntMulExpr that = (IntMulExpr) obj;
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
