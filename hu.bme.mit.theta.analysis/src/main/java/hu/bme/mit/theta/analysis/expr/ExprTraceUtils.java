package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.analysis.Trace;

public final class ExprTraceUtils {

	private ExprTraceUtils() {
	}

	public static Trace<ExprState, ExprAction> traceFrom(final List<? extends ExprAction> actions) {
		checkNotNull(actions);
		final List<ExprState> states = new ArrayList<>(actions.size() + 1);
		for (int i = 0; i < actions.size() + 1; i++) {
			states.add(SimpleExprState.of(True()));
		}
		return Trace.of(states, actions);
	}

}
