package hu.bme.mit.inf.theta.formalism.utils.impl;

import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.impl.ExprCnfCheckerVisitor;
import hu.bme.mit.inf.theta.core.utils.impl.ExprCnfCheckerVisitor.CNFStatus;
import hu.bme.mit.inf.theta.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.theta.formalism.utils.FormalismExprVisitor;

public class FormalismCnfCheckerVisitor extends ExprCnfCheckerVisitor
		implements FormalismExprVisitor<CNFStatus, Boolean> {

	@Override
	public <ExprType extends Type> Boolean visit(final PrimedExpr<ExprType> expr, final CNFStatus param) {
		// A prime counts as a NOT expression, no boolean connective can be
		// inside it
		return expr.getOp().accept(this, CNFStatus.INSIDE_NOT);
	}

	@Override
	public <DeclType extends Type> Boolean visit(final VarRefExpr<DeclType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final ClockRefExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ReturnType extends Type> Boolean visit(final ProcRefExpr<ReturnType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ReturnType extends Type> Boolean visit(final ProcCallExpr<ReturnType> expr, final CNFStatus param) {
		return true;
	}

}
