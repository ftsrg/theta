package hu.bme.mit.theta.analysis.expr;

public interface MultiStackableExprState<P, R extends ExprState, S extends StackableExprState<R>> extends MultiExprState<P, S>{
	MultiStackableExprState<P, R, S> push(P p, R s);

	MultiStackableExprState<P, R, S> pop(P p);
}
