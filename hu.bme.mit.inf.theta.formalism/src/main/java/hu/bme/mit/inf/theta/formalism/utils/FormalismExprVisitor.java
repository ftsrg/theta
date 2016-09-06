package hu.bme.mit.inf.theta.formalism.utils;

import hu.bme.mit.inf.theta.core.utils.ExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.visitor.ClockRefExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.visitor.PrimedExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.visitor.ProcCallExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.visitor.ProcRefExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.visitor.VarRefExprVisitor;

public interface FormalismExprVisitor<P, R> extends ExprVisitor<P, R>, PrimedExprVisitor<P, R>,
		ProcCallExprVisitor<P, R>, ProcRefExprVisitor<P, R>, VarRefExprVisitor<P, R>, ClockRefExprVisitor<P, R> {

}
