package hu.bme.mit.inf.ttmc.formalism.expr.visitor;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.expr.VarRefExpr;

public interface VarRefExprVisitor<P, R> extends ExprVisitor<P, R> {
	public <DeclType extends Type> R visit(VarRefExpr<DeclType> expr, P param);
}
