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

import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import java.util.List;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.MultiaryExpr;

public final class OrExpr extends MultiaryExpr<BoolType, BoolType> {

	private static final int HASH_SEED = 131;

	private static final String OPERATOR_LABEL = "or";

	private OrExpr(final Iterable<? extends Expr<BoolType>> ops) {
		super(ops);
	}

	public static OrExpr of(final Iterable<? extends Expr<BoolType>> ops) {
		return new OrExpr(ops);
	}

	public static OrExpr create(final List<? extends Expr<?>> ops) {
		return OrExpr.of(ops.stream().map(op -> cast(op, Bool())).collect(toImmutableList()));
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Valuation val) {
		for (final Expr<BoolType> op : getOps()) {
			final BoolLitExpr opVal = (BoolLitExpr) op.eval(val);
			if (opVal.getValue()) {
				return True();
			}
		}
		return False();
	}

	@Override
	public OrExpr with(final Iterable<? extends Expr<BoolType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new OrExpr(ops);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof OrExpr) {
			final OrExpr that = (OrExpr) obj;
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
