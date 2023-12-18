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
package hu.bme.mit.theta.core.clock.constr;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.clocktype.ClockDiffExpr;
import hu.bme.mit.theta.core.type.clocktype.ClockExprs;
import hu.bme.mit.theta.core.type.clocktype.ClockGeqExpr;
import hu.bme.mit.theta.core.type.clocktype.ClockType;

public final class DiffGeqConstr extends DiffConstr {

	private static final int HASH_SEED = 4327;

	private static final String OPERATOR_LABEL = ">=";

	private volatile ClockGeqExpr expr = null;

	DiffGeqConstr(final VarDecl<ClockType> leftVar, final VarDecl<ClockType> rightVar, final int bound) {
		super(leftVar, rightVar, bound);
	}

	@Override
	public ClockGeqExpr toExpr() {
		ClockGeqExpr result = expr;
		if (result == null) {
			final RefExpr<ClockType> leftRef = getLeftVar().getRef();
			final RefExpr<ClockType> rightRef = getRightVar().getRef();
			final ClockDiffExpr diffExpr = ClockExprs.Diff(leftRef, rightRef);
			result = ClockExprs.Geq(diffExpr, Int(getBound()));
			expr = result;
		}
		return result;
	}

	@Override
	public <P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DiffGeqConstr) {
			final DiffGeqConstr that = (DiffGeqConstr) obj;
			return this.getBound() == that.getBound() && this.getLeftVar().equals(that.getLeftVar())
					&& this.getRightVar().equals(that.getRightVar());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
