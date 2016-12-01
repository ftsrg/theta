package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public interface ExprState extends State {

	Expr<? extends BoolType> toExpr();
}
