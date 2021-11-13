package hu.bme.mit.theta.xcfa.analysis.common;

import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

public abstract class XcfaState<S extends ExprState> implements ExprState {
	public static XcfaState<ExplState> create(final XcfaLocation currentLoc, final ExplState state) {
		return new SimpleXcfaState<>(currentLoc, state);
	}

	public abstract S getGlobalState();
	public abstract XcfaLocation getCurrentLoc();
	public boolean isError() {
		return getCurrentLoc().isErrorLoc();
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder("XcfaState").add(getCurrentLoc()).add(getGlobalState()).toString();
	}

	private static class SimpleXcfaState<S extends ExprState> extends XcfaState<S> {
		private final XcfaLocation currentLoc;;
		private final S globalState;

		private SimpleXcfaState(final XcfaLocation currentLoc, final S globalState) {
			this.currentLoc = currentLoc;
			this.globalState = globalState;
		}

		@Override
		public boolean isBottom() {
			return globalState.isBottom();
		}

		@Override
		public Expr<BoolType> toExpr() {
			return globalState.toExpr();
		}

		@Override
		public S getGlobalState() {
			return globalState;
		}

		@Override
		public XcfaLocation getCurrentLoc() {
			return currentLoc;
		}
	}
}
