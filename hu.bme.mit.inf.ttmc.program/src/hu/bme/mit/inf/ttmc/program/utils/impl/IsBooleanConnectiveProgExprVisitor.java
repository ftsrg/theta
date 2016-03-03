package hu.bme.mit.inf.ttmc.program.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.IsBooleanConnectiveExprVisitor;
import hu.bme.mit.inf.ttmc.program.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.program.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.program.utils.ProgExprVisitor;

public class IsBooleanConnectiveProgExprVisitor extends IsBooleanConnectiveExprVisitor implements ProgExprVisitor<Void, Boolean> {

	@Override
	public <ExprType extends Type> Boolean visit(PrimedExpr<ExprType> expr, Void param) {
		return false;
	}

	@Override
	public <DeclType extends Type> Boolean visit(VarRefExpr<DeclType> expr, Void param) {
		return false;
	}

	@Override
	public <ReturnType extends Type> Boolean visit(ProcRefExpr<ReturnType> expr, Void param) {
		return false;
	}

	@Override
	public <ReturnType extends Type> Boolean visit(ProcCallExpr<ReturnType> expr, Void param) {
		return false;
	}

}
