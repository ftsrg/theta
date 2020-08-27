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
package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.clock.constr.ClockConstrs.Eq;
import static hu.bme.mit.theta.core.clock.constr.ClockConstrs.Gt;
import static hu.bme.mit.theta.core.clock.constr.ClockConstrs.Lt;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static java.util.stream.Collectors.toList;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.Map;

import com.google.common.collect.Iterables;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.clock.constr.ClockConstr;
import hu.bme.mit.theta.core.clock.op.ClockOp;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class ZoneState implements ExprState {

	private static final ZoneState TOP = new ZoneState(DBM.top(Collections.emptySet()));
	private static final ZoneState BOTTOM = new ZoneState(DBM.bottom(Collections.emptySet()));

	private static final int HASH_SEED = 4349;

	private volatile int hashCode = 0;
	private volatile Expr<BoolType> expr = null;

	private final DBM dbm;

	private ZoneState(final DBM dbm) {
		this.dbm = dbm;
	}

	private ZoneState(final Builder ops) {
		this.dbm = ops.dbm;
	}

	////

	public static ZoneState region(final Valuation valuation, final Collection<VarDecl<RatType>> vars) {
		checkNotNull(valuation);
		final Iterable<VarDecl<RatType>> constrainedVars = Iterables.filter(vars, v -> valuation.eval(v).isPresent());

		final DBM dbm = DBM.top(constrainedVars);

		for (final VarDecl<RatType> x : constrainedVars) {
			final RatLitExpr sx = (RatLitExpr) valuation.eval(x).get();
			final RatLitExpr fx = sx.frac();

			if (fx.getNum().compareTo(BigInteger.ZERO) == 0) {
				dbm.and(Eq(x, sx.getNum().intValue()));
			} else {
				dbm.and(Lt(x, sx.ceil().intValue()));
				dbm.and(Gt(x, sx.floor().intValue()));
			}

			for (final VarDecl<RatType> y : constrainedVars) {
				if (x == y) {
					continue;
				}

				final RatLitExpr sy = (RatLitExpr) valuation.eval(y).get();
				final RatLitExpr fy = sy.frac();

				final int compareResult = fx.compareTo(fy);
				if (compareResult == 0) {
					dbm.and(Eq(x, y, sx.floor().intValue() - sy.floor().intValue()));
				} else if (compareResult < 0) {
					dbm.and(Lt(x, y, sx.floor().intValue() - sy.floor().intValue()));
				}
			}
		}

		return new ZoneState(dbm);
	}

	public static ZoneState top() {
		return TOP;
	}

	public static ZoneState bottom() {
		return BOTTOM;
	}

	public static ZoneState zero(final Collection<? extends VarDecl<RatType>> clocks) {
		return new ZoneState(DBM.zero(clocks));
	}

	public static ZoneState intersection(final ZoneState zone1, final ZoneState zone2) {
		checkNotNull(zone1);
		checkNotNull(zone2);
		return new ZoneState(DBM.intersection(zone1.dbm, zone2.dbm));
	}

	public static ZoneState enclosure(final ZoneState zone1, final ZoneState zone2) {
		checkNotNull(zone1);
		checkNotNull(zone2);
		return new ZoneState(DBM.enclosure(zone1.dbm, zone2.dbm));
	}

	public static ZoneState interpolant(final ZoneState zoneA, final ZoneState zoneB) {
		checkNotNull(zoneA);
		checkNotNull(zoneB);
		return new ZoneState(DBM.interpolant(zoneA.dbm, zoneB.dbm));
	}

	public static ZoneState weakInterpolant(final ZoneState zoneA, final ZoneState zoneB) {
		checkNotNull(zoneA);
		checkNotNull(zoneB);
		return new ZoneState(DBM.weakInterpolant(zoneA.dbm, zoneB.dbm));
	}

	////

	public Collection<ZoneState> complement() {
		final Collection<DBM> dbms = dbm.complement();
		return dbms.stream().map(ZoneState::new).collect(toList());
	}

	public Builder transform() {
		return Builder.transform(this);
	}

	public Builder project(final Collection<? extends VarDecl<RatType>> clocks) {
		checkNotNull(clocks);
		return Builder.project(this, clocks);
	}

	////

	public boolean isTop() {
		return DBM.top(Collections.emptySet()).getRelation(dbm) == DbmRelation.EQUAL;
	}

	@Override
	public boolean isBottom() {
		return !dbm.isConsistent();
	}

	public boolean isLeq(final ZoneState that) {
		return this.dbm.isLeq(that.dbm);
	}

	public boolean isLeq(final ZoneState that, final Collection<? extends VarDecl<RatType>> activeVars) {
		return this.dbm.isLeq(that.dbm, activeVars);
	}

	public boolean isLeq(final ZoneState that, final BoundFunc boundFunction) {
		return this.dbm.isLeq(that.dbm, boundFunction);
	}

	public boolean isConsistentWith(final ZoneState that) {
		return this.dbm.isConsistentWith(that.dbm);
	}

	////

	@Override
	public Expr<BoolType> toExpr() {
		Expr<BoolType> result = expr;
		if (result == null) {
			final Collection<Expr<BoolType>> exprs = dbm.getConstrs().stream().map(ClockConstr::toExpr)
					.collect(toList());
			result = And(exprs);
			expr = result;
		}
		return result;
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + dbm.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ZoneState) {
			final ZoneState that = (ZoneState) obj;
			return this.dbm.equals(that.dbm);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final Collection<ClockConstr> constrs = dbm.getConstrs();
		return Utils.lispStringBuilder(getClass().getSimpleName()).aligned().addAll(constrs).toString();
	}

	////////

	public static class Builder {
		private final DBM dbm;

		private Builder(final DBM dbm) {
			this.dbm = dbm;
		}

		////

		private static Builder transform(final ZoneState state) {
			return new Builder(DBM.copyOf(state.dbm));
		}

		private static Builder project(final ZoneState state, final Collection<? extends VarDecl<RatType>> clocks) {
			return new Builder(DBM.project(state.dbm, clocks));
		}

		////

		public ZoneState build() {
			return new ZoneState(this);
		}

		////

		public Builder up() {
			dbm.up();
			return this;
		}

		public Builder down() {
			dbm.down();
			return this;
		}

		public Builder nonnegative() {
			dbm.nonnegative();
			return this;
		}

		public Builder execute(final ClockOp op) {
			dbm.execute(op);
			return this;
		}

		public Builder and(final ClockConstr constr) {
			dbm.and(constr);
			return this;
		}

		public Builder free(final VarDecl<RatType> varDecl) {
			dbm.free(varDecl);
			return this;
		}

		public Builder reset(final VarDecl<RatType> varDecl, final int m) {
			dbm.reset(varDecl, m);
			return this;
		}

		public Builder copy(final VarDecl<RatType> lhs, final VarDecl<RatType> rhs) {
			dbm.copy(lhs, rhs);
			return this;
		}

		public Builder shift(final VarDecl<RatType> varDecl, final int m) {
			dbm.shift(varDecl, m);
			return this;
		}

		public Builder norm(final Map<? extends VarDecl<RatType>, ? extends Integer> ceilings) {
			dbm.norm(ceilings);
			return this;
		}
	}

}
