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
package hu.bme.mit.theta.xta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class ItpZoneState implements ExprState {

	private static final int HASH_SEED = 3361;
	private volatile int hashCode = 0;

	private final ZoneState zone;
	private final ZoneState interpolant;

	private ItpZoneState(final ZoneState zone, final ZoneState interpolant) {
		checkNotNull(zone);
		checkNotNull(interpolant);

		assert zone.isLeq(interpolant);

		this.zone = zone;
		this.interpolant = interpolant;
	}

	public static ItpZoneState of(final ZoneState state, final ZoneState interpolant) {
		return new ItpZoneState(state, interpolant);
	}

	////

	public ZoneState getZone() {
		return zone;
	}

	public ZoneState getInterpolant() {
		return interpolant;
	}

	////

	public boolean isLeq(final ItpZoneState that) {
		return this.interpolant.isLeq(that.interpolant);
	}

	////

	public ItpZoneState withState(final ZoneState state) {
		return ItpZoneState.of(state, this.interpolant);
	}

	public ItpZoneState withInterpolant(final ZoneState interpolant) {
		return ItpZoneState.of(this.zone, interpolant);
	}

	////

	@Override
	public boolean isBottom() {
		return zone.isBottom();
	}

	@Override
	public Expr<BoolType> toExpr() {
		if (isBottom()) {
			return False();
		} else {
			return interpolant.toExpr();
		}
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + zone.hashCode();
			result = 37 * result + interpolant.hashCode();
			result = hashCode;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ItpZoneState) {
			final ItpZoneState that = (ItpZoneState) obj;
			return this.zone.equals(that.zone) && this.interpolant.equals(that.interpolant);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return interpolant.toString();
	}

}
