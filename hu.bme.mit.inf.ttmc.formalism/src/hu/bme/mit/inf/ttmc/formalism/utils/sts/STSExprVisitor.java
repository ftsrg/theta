package hu.bme.mit.inf.ttmc.formalism.utils.sts;

import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.PrimedExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.VarRefExprVisitor;

public interface STSExprVisitor<P, R> extends
	ExprVisitor<P, R>,
	PrimedExprVisitor<P, R>,
	VarRefExprVisitor<P, R> {
}
