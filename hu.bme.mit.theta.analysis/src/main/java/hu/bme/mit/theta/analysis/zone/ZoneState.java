package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs.Eq;
import static hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs.Gt;
import static hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs.Lt;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.Collections;
import java.util.Map;

import com.google.common.collect.Iterables;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.RatLitExpr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.op.ClockOp;

public final class ZoneState implements ExprState {

	private static final ZoneState TOP = new ZoneState(DBM.top(Collections.emptySet()));
	private static final ZoneState BOTTOM = new ZoneState(DBM.bottom(Collections.emptySet()));

	private static final int HASH_SEED = 4349;

	private volatile int hashCode = 0;
	private volatile Expr<? extends BoolType> expr = null;

	private final DBM dbm;

	private ZoneState(final DBM dbm) {
		this.dbm = dbm;
	}

	private ZoneState(final Builder ops) {
		this.dbm = ops.dbm;
	}

	////

	public static ZoneState region(final Valuation valuation) {
		checkNotNull(valuation);
		final Iterable<ClockDecl> clocks = Iterables.filter(valuation.getDecls(), ClockDecl.class);

		final DBM dbm = DBM.top(clocks);

		for (final ClockDecl c : clocks) {
			final RatLitExpr sc = (RatLitExpr) valuation.eval(c).get();
			final RatLitExpr fc = sc.frac();

			if (fc.getNum() == 0) {
				dbm.and(Eq(c, sc.getNum()));
			} else {
				dbm.and(Lt(c, sc.ceil()));
				dbm.and(Gt(c, sc.floor()));
			}

			for (final ClockDecl d : clocks) {
				if (c == d) {
					continue;
				}

				final RatLitExpr sd = (RatLitExpr) valuation.eval(d).get();
				final RatLitExpr fd = sd.frac();

				final int compareResult = fc.compareTo(fd);
				if (compareResult == 0) {
					dbm.and(Eq(c, d, sc.floor() - sd.floor()));
				} else if (compareResult < 0) {
					dbm.and(Lt(c, d, sc.floor() - sd.floor()));
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

	public static ZoneState zero(final Collection<? extends ClockDecl> clocks) {
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

	////

	public Collection<ZoneState> complement() {
		final Collection<DBM> dbms = dbm.complement();
		return dbms.stream().map(ZoneState::new).collect(toList());
	}

	public Builder transform() {
		return Builder.transform(this);
	}

	public Builder project(final Collection<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		return Builder.project(this, clocks);
	}

	////

	public boolean isTop() {
		return DBM.top(Collections.emptySet()).getRelation(dbm) == DbmRelation.EQUAL;
	}

	public boolean isBottom() {
		return !dbm.isConsistent();
	}

	public boolean isLeq(final ZoneState that) {
		return this.dbm.getRelation(that.dbm).isLeq();
	}

	public boolean isConsistentWith(final ZoneState that) {
		return this.dbm.isConsistentWith(that.dbm);
	}

	////

	@Override
	public Expr<? extends BoolType> toExpr() {
		Expr<? extends BoolType> result = expr;
		if (result == null) {
			final Collection<Expr<? extends BoolType>> exprs = dbm.getConstrs().stream().map(ClockConstr::toExpr)
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
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(dbm.getConstrs()).toString();
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

		private static Builder project(final ZoneState state, final Collection<? extends ClockDecl> clocks) {
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

		public Builder execute(final ClockOp op) {
			dbm.execute(op);
			return this;
		}

		public Builder and(final ClockConstr constr) {
			dbm.and(constr);
			return this;
		}

		public Builder free(final ClockDecl clock) {
			dbm.free(clock);
			return this;
		}

		public Builder reset(final ClockDecl clock, final int m) {
			dbm.reset(clock, m);
			return this;
		}

		public Builder copy(final ClockDecl lhs, final ClockDecl rhs) {
			dbm.copy(lhs, rhs);
			return this;
		}

		public Builder shift(final ClockDecl clock, final int m) {
			dbm.shift(clock, m);
			return this;
		}

		public Builder norm(final Map<? extends ClockDecl, ? extends Integer> ceilings) {
			dbm.norm(ceilings);
			return this;
		}
	}

}
