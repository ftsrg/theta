package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.expr.ExprStateUtils.anyUncoveredSuccessor;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;
import static java.util.Collections.singleton;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.solver.Solver;

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

	public static boolean isInductive(final Trace<? extends ExprState, ? extends ExprAction> trace,
			final Solver solver) {
		for (int i = 0; i < trace.length(); i++) {
			final ExprState sourceState = trace.getState(i);
			final ExprAction action = trace.getAction(i);
			final ExprState targetState = trace.getState(i + 1);

			final Optional<Valuation> uncoveredSuccessor = anyUncoveredSuccessor(sourceState, action,
					singleton(targetState), solver);
			if (uncoveredSuccessor.isPresent()) {
				return false;
			}
		}
		return true;
	}

}
