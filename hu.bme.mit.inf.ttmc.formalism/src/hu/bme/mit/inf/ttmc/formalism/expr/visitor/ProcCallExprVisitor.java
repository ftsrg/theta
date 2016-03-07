package hu.bme.mit.inf.ttmc.formalism.expr.visitor;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.expr.ProcCallExpr;

public interface ProcCallExprVisitor<P, R> extends ExprVisitor<P, R> {
	public <ReturnType extends Type> R visit(ProcCallExpr<ReturnType> expr, P param);
}
