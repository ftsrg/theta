package hu.bme.mit.theta.formalism.common.expr.visitor;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;
import hu.bme.mit.theta.formalism.common.expr.VarRefExpr;

public interface VarRefExprVisitor<P, R> extends ExprVisitor<P, R> {
	public <DeclType extends Type> R visit(VarRefExpr<DeclType> expr, P param);
}
