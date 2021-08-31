package hu.bme.mit.theta.analysis.expr;

import java.util.Map;

public interface MultiExprState<P, S extends ExprState> extends ExprState{
	MultiExprState<P, S> add(P p, S s);

	MultiExprState<P, S> remove(P p);

	MultiExprState<P, S> update(P p, S s);

	Map<P, S> getStates();
}
