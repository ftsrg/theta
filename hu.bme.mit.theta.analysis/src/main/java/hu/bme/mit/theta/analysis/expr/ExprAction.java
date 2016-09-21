package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public interface ExprAction extends Action {

	public Expr<? extends BoolType> toExpr();

}
