package hu.bme.mit.inf.ttmc.formalism.utils.sts;

import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.expr.visitor.PrimedExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.expr.visitor.VarRefExprVisitor;

public interface STSExprVisitor<P, R> extends
	ExprVisitor<P, R>,
	PrimedExprVisitor<P, R>,
	VarRefExprVisitor<P, R> {
}
