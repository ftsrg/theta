package hu.bme.mit.theta.analysis.expr;

import java.util.List;

public interface StackableExprState<S extends ExprState> extends ExprState {
	StackableExprState<S> push(S s);

	StackableExprState<S> pop();

	S peek();

	List<S> getStates();
}
