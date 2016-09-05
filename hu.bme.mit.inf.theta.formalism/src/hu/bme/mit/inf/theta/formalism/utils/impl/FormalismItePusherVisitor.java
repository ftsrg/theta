package hu.bme.mit.inf.theta.formalism.utils.impl;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.impl.ExprItePusherVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.theta.formalism.utils.FormalismExprVisitor;

public class FormalismItePusherVisitor extends ExprItePusherVisitor
		implements FormalismExprVisitor<Void, Expr<? extends Type>> {

	public FormalismItePusherVisitor() {
		super();
	}

	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(final PrimedExpr<ExprType> expr, final Void param) {
		return visitUnary(expr, param);
	}

	@Override
	public <DeclType extends Type> Expr<? extends Type> visit(final VarRefExpr<DeclType> expr, final Void param) {
		return visitNullary(expr, param);
	}

	@Override
	public Expr<? extends Type> visit(final ClockRefExpr expr, final Void param) {
		return visitNullary(expr, param);
	}

	@Override
	public <ReturnType extends Type> Expr<? extends Type> visit(final ProcRefExpr<ReturnType> expr, final Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ReturnType extends Type> Expr<? extends Type> visit(final ProcCallExpr<ReturnType> expr, final Void param) {
		throw new UnsupportedOperationException("TODO");
	}

}
