package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Prime;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.model.Assignment;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprSimplifierVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public class FormalismExprSimplifierVisitor extends ExprSimplifierVisitor implements FormalismExprVisitor<Assignment, Expr<? extends Type>> {

	@Override
	public <ExprType extends Type> Expr<? extends ExprType> visit(final PrimedExpr<ExprType> expr, final Assignment param) {
		@SuppressWarnings("unchecked")
		final Expr<? extends ExprType> op = (Expr<? extends ExprType>) expr.getOp().accept(this, param);

		return Prime(op);
	}

	@Override
	public <ReturnType extends Type> Expr<? extends Type> visit(final ProcCallExpr<ReturnType> expr, final Assignment param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ReturnType extends Type> Expr<? extends Type> visit(final ProcRefExpr<ReturnType> expr, final Assignment param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <DeclType extends Type> Expr<? extends DeclType> visit(final VarRefExpr<DeclType> expr, final Assignment param) {
		return expr;
	}

}
