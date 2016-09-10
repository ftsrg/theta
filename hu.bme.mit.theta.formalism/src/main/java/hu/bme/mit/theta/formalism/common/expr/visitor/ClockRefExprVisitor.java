package hu.bme.mit.theta.formalism.common.expr.visitor;

import hu.bme.mit.theta.core.utils.ExprVisitor;
import hu.bme.mit.theta.formalism.common.expr.ClockRefExpr;

public interface ClockRefExprVisitor<P, R> extends ExprVisitor<P, R> {
	public R visit(ClockRefExpr expr, P param);
}