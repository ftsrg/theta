package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.IsBoolConnExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public class IsBoolConnFormalismExprVisitor extends IsBoolConnExprVisitor
		implements FormalismExprVisitor<Void, Boolean> {

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
