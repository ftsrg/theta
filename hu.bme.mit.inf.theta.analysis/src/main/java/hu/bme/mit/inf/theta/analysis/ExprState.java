package hu.bme.mit.inf.theta.analysis;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;

public interface ExprState extends State {

	Expr<? extends BoolType> toExpr();
}
