package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprITEPropagatorVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public class FormalismITEPropagatorVisitor extends ExprITEPropagatorVisitor
		implements FormalismExprVisitor<Void, Expr<? extends Type>> {

	public FormalismITEPropagatorVisitor(
			final FormalismExprVisitor<Void, Expr<? extends Type>> formalismITEPusherVisitor) {
		super(formalismITEPusherVisitor);
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
