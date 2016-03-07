package hu.bme.mit.inf.ttmc.program.utils;

import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.program.expr.visitor.PrimedExprVisitor;
import hu.bme.mit.inf.ttmc.program.expr.visitor.ProcCallExprVisitor;
import hu.bme.mit.inf.ttmc.program.expr.visitor.ProcRefExprVisitor;
import hu.bme.mit.inf.ttmc.program.expr.visitor.VarRefExprVisitor;

public interface AllExprVisitor<P, R> extends
	ExprVisitor<P, R>,
	PrimedExprVisitor<P, R>,
	ProcCallExprVisitor<P, R>,
	ProcRefExprVisitor<P, R>,
	VarRefExprVisitor<P, R> {

}
