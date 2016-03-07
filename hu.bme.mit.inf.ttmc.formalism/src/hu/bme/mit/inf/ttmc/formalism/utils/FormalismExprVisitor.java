package hu.bme.mit.inf.ttmc.formalism.utils;

import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.expr.visitor.PrimedExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.expr.visitor.ProcCallExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.expr.visitor.ProcRefExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.expr.visitor.VarRefExprVisitor;

public interface FormalismExprVisitor<P, R> extends
	ExprVisitor<P, R>,
	PrimedExprVisitor<P, R>,
	ProcCallExprVisitor<P, R>,
	ProcRefExprVisitor<P, R>,
	VarRefExprVisitor<P, R> {

}
