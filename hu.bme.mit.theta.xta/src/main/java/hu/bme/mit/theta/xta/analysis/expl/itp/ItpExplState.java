/*
 *  Copyright 2018 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.analysis.expl.itp;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class ItpExplState implements ExprState {
	private final ExplState concrState;
	private final ExplState abstrState;

	private static final int HASH_SEED = 7211;
	private volatile int hashCode = 0;

	private ItpExplState(final ExplState concrState, final ExplState abstrState) {
		this.concrState = checkNotNull(concrState);
		this.abstrState = checkNotNull(abstrState);
		assert concrState.isLeq(abstrState);
	}

	public static ItpExplState of(final ExplState concrState, final ExplState abstrState) {
		return new ItpExplState(concrState, abstrState);
	}

	public ExplState getConcrState() {
		return concrState;
	}

	public ExplState getAbstrState() {
		return abstrState;
	}

	public ItpExplState withConcrState(final ExplState concrState) {
		return ItpExplState.of(concrState, abstrState);
	}

	public ItpExplState withAbstrState(final ExplState abstrState) {
		return ItpExplState.of(concrState, abstrState);
	}

	@Override
	public boolean isBottom() {
		return concrState.isBottom();
	}

	@Override
	public Expr<BoolType> toExpr() {
		if (isBottom()) {
			return False();
		} else {
			return abstrState.toExpr();
		}
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + concrState.hashCode();
			result = 37 * result + abstrState.hashCode();
			result = hashCode;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ItpExplState) {
			final ItpExplState that = (ItpExplState) obj;
			return this.concrState.equals(that.concrState) && this.abstrState.equals(that.abstrState);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
