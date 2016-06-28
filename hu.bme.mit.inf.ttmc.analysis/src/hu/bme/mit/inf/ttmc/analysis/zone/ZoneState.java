package hu.bme.mit.inf.ttmc.analysis.zone;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;

public final class ZoneState implements State {

	private static final int HASH_SEED = 4349;

	private volatile int hashCode = 0;

	private final DBM dbm;

	private ZoneState(final DBM dbm) {
		this.dbm = dbm;
	}

	private ZoneState(final ZoneOperations ops) {
		this.dbm = ops.dbm;
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

	public boolean isBottom() {
		return !dbm.isConsistent();
	}

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
		return "ZoneState";
	}

	////////

	public static class ZoneOperations {

		private final DBM dbm;

		private ZoneOperations(final ZoneState zone) {
			dbm = DBM.copyOf(zone.dbm);
		}

		////////

		public ZoneState done() {
			return new ZoneState(this);
		}

		////////

		public ZoneOperations up() {
			dbm.up();
			return this;
		}

		public ZoneOperations down() {
			dbm.down();
			return this;
		}

		public ZoneOperations execute(final ClockOp op) {
			dbm.execute(op);
			return this;
		}

		public ZoneOperations and(final ClockConstr constr) {
			dbm.and(constr);
			return this;
		}

		public ZoneOperations free(final ClockDecl clock) {
			dbm.free(clock);
			return this;
		}

		public ZoneOperations reset(final ClockDecl clock, final int m) {
			dbm.reset(clock, m);
			return this;
		}

		public ZoneOperations copy(final ClockDecl lhs, final ClockDecl rhs) {
			dbm.copy(lhs, rhs);
			return this;
		}

		public ZoneOperations shift(final ClockDecl clock, final int m) {
			dbm.shift(clock, m);
			return this;
		}
	}
}
