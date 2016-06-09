package hu.bme.mit.inf.ttmc.analysis.zone;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;

public final class ZoneState implements State {

	private static final int HASH_SEED = 4349;

	private volatile int hashCode = 0;

	private final DBM dbm;

	private ZoneState(final DBM dbm) {
		this.dbm = dbm;
	}

	private ZoneState(final ZoneOperations ops) {
		this.dbm = ops.builder.build();
	}

	////

	public static ZoneState top(final Collection<? extends ClockDecl> clocks) {
		return new ZoneState(DBM.top(clocks));
	}

	public static ZoneState zero(final Collection<? extends ClockDecl> clocks) {
		return new ZoneState(DBM.zero(clocks));
	}

	////

	public ZoneOperations transform() {
		return new ZoneOperations(this);
	}

	////

	public boolean isLeq(final ZoneState that) {
		return this.dbm.getRelation(that.dbm).isLeq();
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
		return dbm.toString();
	}

	////////

	public static class ZoneOperations {
		private final DBMBuilder builder;

		private ZoneOperations(final ZoneState zone) {
			builder = zone.dbm.transform();
		}

		////////

		public ZoneState done() {
			return new ZoneState(this);
		}

		////////

		public ZoneOperations up() {
			builder.up();
			return this;
		}

		public ZoneOperations down() {
			builder.down();
			return this;
		}

		public ZoneOperations and(final ClockConstr constr) {
			builder.and(constr);
			return this;
		}

		public ZoneOperations free(final ClockDecl clock) {
			builder.free(clock);
			return this;
		}

		public ZoneOperations reset(final ClockDecl clock, final int m) {
			builder.reset(clock, m);
			return this;
		}

		public ZoneOperations copy(final ClockDecl lhs, final ClockDecl rhs) {
			builder.copy(lhs, rhs);
			return this;
		}

		public ZoneOperations shift(final ClockDecl clock, final int m) {
			builder.shift(clock, m);
			return this;
		}
	}
}
