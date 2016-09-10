package hu.bme.mit.theta.formalism.utils;

import hu.bme.mit.theta.core.utils.ExprVisitor;
import hu.bme.mit.theta.formalism.common.expr.visitor.PrimedExprVisitor;
import hu.bme.mit.theta.formalism.common.expr.visitor.ProcCallExprVisitor;
import hu.bme.mit.theta.formalism.common.expr.visitor.ProcRefExprVisitor;
import hu.bme.mit.theta.formalism.common.expr.visitor.VarRefExprVisitor;

public interface ProgExprVisitor<P, R> extends 
	ExprVisitor<P, R>,
	PrimedExprVisitor<P, R>,
	ProcCallExprVisitor<P, R>,
	ProcRefExprVisitor<P, R>,
	VarRefExprVisitor<P, R> {

}
