package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.tcfa.TcfaUtils.isClockExpr;
import static hu.bme.mit.theta.analysis.tcfa.TcfaUtils.isDataExpr;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs;

public abstract class TcfaInvar {

	private TcfaInvar() {
	}

	public static TcfaInvar of(final Expr<? extends BoolType> expr) {
		checkNotNull(expr);
		if (isClockExpr(expr)) {
			final ClockConstr constr = ClockConstrs.formExpr(expr);
			return new ClockInvar(constr);
		} else if (isDataExpr(expr)) {
			return new DataInvar(expr);
		} else {
			throw new AssertionError();
		}
	}

	public abstract boolean isClockInvar();

	public abstract boolean isDataInvar();

	public abstract ClockInvar asClockInvar();

	public abstract DataInvar asDataInvar();

	////

	public static final class ClockInvar extends TcfaInvar {
		private final ClockConstr constr;

		private ClockInvar(final ClockConstr constr) {
			this.constr = checkNotNull(constr);
		}

		public ClockConstr getConstr() {
			return constr;
		}

		@Override
		public boolean isClockInvar() {
			return true;
		}

		@Override
		public boolean isDataInvar() {
			return false;
		}

		@Override
		public ClockInvar asClockInvar() {
			return this;
		}

		@Override
		public DataInvar asDataInvar() {
			throw new ClassCastException();
		}
	}

	public static final class DataInvar extends TcfaInvar {
		private final Expr<? extends BoolType> expr;

		private DataInvar(final Expr<? extends BoolType> expr) {
			this.expr = checkNotNull(expr);
		}

		public Expr<? extends BoolType> getExpr() {
			return expr;
		}

		@Override
		public boolean isClockInvar() {
			return false;
		}

		@Override
		public boolean isDataInvar() {
			return true;
		}

		@Override
		public ClockInvar asClockInvar() {
			throw new ClassCastException();
		}

		@Override
		public DataInvar asDataInvar() {
			return this;
		}
	}

}
