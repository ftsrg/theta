package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs;

public abstract class TcfaExpr {
	private final Expr<? extends BoolType> expr;

	private TcfaExpr(final Expr<? extends BoolType> expr) {
		this.expr = checkNotNull(expr);
	}

	public static TcfaExpr of(final Expr<? extends BoolType> expr) {
		checkNotNull(expr);
		if (TcfaUtils.isClockExpr(expr)) {
			return new ClockExpr(expr);
		} else if (TcfaUtils.isDataExpr(expr)) {
			return new DataExpr(expr);
		} else {
			throw new AssertionError();
		}
	}

	public final Expr<? extends BoolType> getExpr() {
		return expr;
	}

	public abstract boolean isClockExpr();

	public abstract boolean isDataExpr();

	public abstract ClockExpr asClockExpr();

	public abstract DataExpr asDataExpr();

	////

	public static final class ClockExpr extends TcfaExpr {
		private final ClockConstr clockConstr;

		private ClockExpr(final Expr<? extends BoolType> expr) {
			super(expr);
			clockConstr = ClockConstrs.formExpr(expr);
		}

		public ClockConstr getClockConstr() {
			return clockConstr;
		}

		@Override
		public boolean isClockExpr() {
			return true;
		}

		@Override
		public boolean isDataExpr() {
			return false;
		}

		@Override
		public ClockExpr asClockExpr() {
			return this;
		}

		@Override
		public DataExpr asDataExpr() {
			throw new ClassCastException();
		}
	}

	public static final class DataExpr extends TcfaExpr {

		private DataExpr(final Expr<? extends BoolType> expr) {
			super(expr);
		}

		@Override
		public boolean isClockExpr() {
			return false;
		}

		@Override
		public boolean isDataExpr() {
			return true;
		}

		@Override
		public ClockExpr asClockExpr() {
			throw new ClassCastException();
		}

		@Override
		public DataExpr asDataExpr() {
			return this;
		}
	}

}
