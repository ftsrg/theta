package hu.bme.mit.theta.formalism.common.expr.visitor;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;
import hu.bme.mit.theta.formalism.common.expr.PrimedExpr;

public interface PrimedExprVisitor<P, R> extends ExprVisitor<P, R> {
	public <ExprType extends Type> R visit(PrimedExpr<ExprType> expr, P param);
}
