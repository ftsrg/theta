package hu.bme.mit.theta.analysis.algorithm.lazy.expr;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public interface ExprActionPre<A extends Action> {
    Expr<BoolType> pre(final Expr<BoolType> state, final A action);
}
