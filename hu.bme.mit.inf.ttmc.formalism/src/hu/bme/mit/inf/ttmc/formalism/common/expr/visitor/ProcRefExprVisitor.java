package hu.bme.mit.inf.ttmc.formalism.common.expr.visitor;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;

public interface ProcRefExprVisitor<P, R> extends ExprVisitor<P, R> {
	public <ReturnType extends Type> R visit(ProcRefExpr<ReturnType> expr, P param);
}
