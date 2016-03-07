package hu.bme.mit.inf.ttmc.program.utils.sts;

import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.program.expr.visitor.PrimedExprVisitor;
import hu.bme.mit.inf.ttmc.program.expr.visitor.VarRefExprVisitor;

public interface STSExprVisitor<P, R> extends
	ExprVisitor<P, R>,
	PrimedExprVisitor<P, R>,
	VarRefExprVisitor<P, R> {
}
