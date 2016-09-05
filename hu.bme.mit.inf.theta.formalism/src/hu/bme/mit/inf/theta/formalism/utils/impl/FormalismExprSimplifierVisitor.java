package hu.bme.mit.inf.theta.formalism.utils.impl;

import static hu.bme.mit.inf.theta.formalism.common.expr.impl.Exprs2.Prime;

import java.util.Optional;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.model.Assignment;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.impl.ExprSimplifierVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.theta.formalism.utils.FormalismExprVisitor;

public class FormalismExprSimplifierVisitor extends ExprSimplifierVisitor
		implements FormalismExprVisitor<Assignment, Expr<? extends Type>> {

	@Override
	public <ExprType extends Type> Expr<? extends ExprType> visit(final PrimedExpr<ExprType> expr,
			final Assignment param) {
		@SuppressWarnings("unchecked")
		final Expr<? extends ExprType> op = (Expr<? extends ExprType>) expr.getOp().accept(this, param);

		return Prime(op);
	}

	@Override
	public <ReturnType extends Type> Expr<? extends Type> visit(final ProcCallExpr<ReturnType> expr,
			final Assignment param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ReturnType extends Type> Expr<? extends Type> visit(final ProcRefExpr<ReturnType> expr,
			final Assignment param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <DeclType extends Type> Expr<? extends DeclType> visit(final VarRefExpr<DeclType> expr,
			final Assignment param) {
		final Optional<? extends Expr<DeclType>> eval = param.eval(expr.getDecl());
		if (eval.isPresent()) {
			return eval.get();
		}

		return expr;
	}

	@Override
	public Expr<? extends Type> visit(final ClockRefExpr expr, final Assignment param) {
		return visit((VarRefExpr<?>) expr, param);
	}

}
