package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprCNFCheckerVisitor;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprCNFCheckerVisitor.CNFStatus;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public class FormalismCNFCheckerVisitor extends ExprCNFCheckerVisitor
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
