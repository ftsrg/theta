package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.VarIndexes;

public interface ExprAction extends Action {

	public Expr<? extends BoolType> toExpr();

	public VarIndexes nextIndexes();

}
