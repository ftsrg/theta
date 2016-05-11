package hu.bme.mit.inf.ttmc.analysis;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface ExprState extends State {

	Expr<? extends BoolType> asExpr();
}
