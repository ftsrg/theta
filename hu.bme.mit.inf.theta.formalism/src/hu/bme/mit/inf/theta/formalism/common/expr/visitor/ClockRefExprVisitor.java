package hu.bme.mit.inf.theta.formalism.common.expr.visitor;

import hu.bme.mit.inf.theta.core.utils.ExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.ClockRefExpr;

public interface ClockRefExprVisitor<P, R> extends ExprVisitor<P, R> {
	public R visit(ClockRefExpr expr, P param);
}