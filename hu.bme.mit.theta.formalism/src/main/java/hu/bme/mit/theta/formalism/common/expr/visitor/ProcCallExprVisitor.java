package hu.bme.mit.theta.formalism.common.expr.visitor;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;
import hu.bme.mit.theta.formalism.common.expr.ProcCallExpr;

public interface ProcCallExprVisitor<P, R> extends ExprVisitor<P, R> {
	public <ReturnType extends Type> R visit(ProcCallExpr<ReturnType> expr, P param);
}
