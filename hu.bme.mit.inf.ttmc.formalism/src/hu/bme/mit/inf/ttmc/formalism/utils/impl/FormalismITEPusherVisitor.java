package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprITEPusherVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public class FormalismITEPusherVisitor extends ExprITEPusherVisitor implements FormalismExprVisitor<Void, Expr<? extends Type>> {

	public FormalismITEPusherVisitor(ConstraintManager manager) {
		super(manager, new IsBoolConnFormalismExprVisitor());
	}

	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(PrimedExpr<ExprType> expr, Void param) {
		return visitUnary(expr, param);
	}

	@Override
	public <DeclType extends Type> Expr<? extends Type> visit(VarRefExpr<DeclType> expr, Void param) {
		return visitNullary(expr, param);
	}

	@Override
	public <ReturnType extends Type> Expr<? extends Type> visit(ProcRefExpr<ReturnType> expr, Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ReturnType extends Type> Expr<? extends Type> visit(ProcCallExpr<ReturnType> expr, Void param) {
		throw new UnsupportedOperationException("TODO");
	}
}
