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

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.PosExpr;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class IntPosExpr extends PosExpr<IntType> {

	private static final int HASH_SEED = 3547;
	private static final String OPERATOR_LABEL = "+";

	private IntPosExpr(final Expr<IntType> op) {
		super(op);
	}

	public static IntPosExpr of(final Expr<IntType> op) {
		return new IntPosExpr(op);
	}

	public static IntPosExpr create(final Expr<?> op) {
		final Expr<IntType> newOp = cast(op, Int());
		return IntPosExpr.of(newOp);
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntLitExpr eval(final Valuation val) {
		final IntLitExpr opVal = (IntLitExpr) getOp().eval(val);
		return opVal.pos();
	}

	@Override
	public IntPosExpr with(final Expr<IntType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return IntPosExpr.of(op);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IntPosExpr) {
			final IntPosExpr that = (IntPosExpr) obj;
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
