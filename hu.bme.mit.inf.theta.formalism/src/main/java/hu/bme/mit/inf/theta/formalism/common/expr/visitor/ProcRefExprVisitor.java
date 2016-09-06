package hu.bme.mit.inf.theta.formalism.common.expr.visitor;

import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcRefExpr;

public interface ProcRefExprVisitor<P, R> extends ExprVisitor<P, R> {
	public <ReturnType extends Type> R visit(ProcRefExpr<ReturnType> expr, P param);
}
