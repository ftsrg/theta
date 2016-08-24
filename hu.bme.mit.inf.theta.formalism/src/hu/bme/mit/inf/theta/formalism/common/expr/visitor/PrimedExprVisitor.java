package hu.bme.mit.inf.theta.formalism.common.expr.visitor;

import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.PrimedExpr;

public interface PrimedExprVisitor<P, R> extends ExprVisitor<P, R> {
	public <ExprType extends Type> R visit(PrimedExpr<ExprType> expr, P param);
}
