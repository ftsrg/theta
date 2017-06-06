package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public interface ExprState extends State {

	Expr<BoolType> toExpr();
}
