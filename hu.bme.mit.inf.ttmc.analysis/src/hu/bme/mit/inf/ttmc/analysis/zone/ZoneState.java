package hu.bme.mit.inf.ttmc.analysis.zone;

import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;

public final class ZoneState implements State {

	private static final int HASH_SEED = 4349;

	private volatile int hashCode = 0;

	private final DBMWithSignature dbm;

	private ZoneState(final DBMWithSignature dbm) {
		this.dbm = dbm;
	}

	private ZoneState(final ZoneOperations transformer) {
		this.dbm = transformer.dbm;
	}

	////

	public static ZoneState zero(final Set<? extends ClockDecl> clockDecls) {
		final DBMWithSignature dbm = DBMWithSignature.zero(clockDecls);
		return new ZoneState(dbm);
	}

	public static ZoneState nonNegative(final Set<? extends ClockDecl> clockDecls) {
		final DBMWithSignature dbm = DBMWithSignature.nonNegative(clockDecls);
		return new ZoneState(dbm);
	}

	public static ZoneState top(final Set<? extends ClockDecl> clockDecls) {
		final DBMWithSignature dbm = DBMWithSignature.top(clockDecls);
		return new ZoneState(dbm);
	}

	////

	public ZoneOperations transform() {
		return new ZoneOperations(this);
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
		private final DBMWithSignature dbm;

		private ZoneOperations(final ZoneState zone) {
			dbm = DBMWithSignature.copyOf(zone.dbm);
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
