package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaProcessState<S extends ExprState> implements ExprState {
	private final S state;
	private final XcfaLocation location;

	private XcfaProcessState(final S state, final XcfaLocation location) {
		this.state = checkNotNull(state);
		this.location = checkNotNull(location);
	}

	public static <S extends ExprState> XcfaProcessState<S> create(final S state, final XcfaLocation location) {
		return new XcfaProcessState<>(state, location);
	}

	@Override
	public boolean isBottom() {
		return state.isBottom();
	}

	@Override
	public Expr<BoolType> toExpr() {
		return state.toExpr();
	}

	public XcfaLocation getLocation() {
		return location;
	}
}
