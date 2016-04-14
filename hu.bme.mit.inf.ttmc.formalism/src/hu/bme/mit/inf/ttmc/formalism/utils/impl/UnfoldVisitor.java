package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprRewriterVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.ProgExprVisitor;

public class UnfoldVisitor extends ExprRewriterVisitor<Integer> implements ProgExprVisitor<Integer, Expr<?>> {

	final VarMap varMap;

	public UnfoldVisitor(final VarMap varMap) {
		this.varMap = varMap;
	}

	////

	@Override
	public <ExprType extends Type> Expr<? extends ExprType> visit(final PrimedExpr<ExprType> expr, final Integer param) {
		final int i = param;
		final Expr<? extends ExprType> op = expr.getOp();
		@SuppressWarnings("unchecked")
		final Expr<? extends ExprType> res = (Expr<? extends ExprType>) op.accept(this, i + 1);
		return res;
	}

	@Override
	public <DeclType extends Type> Expr<? extends DeclType> visit(final VarRefExpr<DeclType> expr, final Integer param) {
		final int i = param;
		final VarDecl<DeclType> varDecl = expr.getDecl();
		final ConstDecl<DeclType> constDecl = varMap.getConstDecl(varDecl, i);
		final ConstRefExpr<DeclType> constRefExpr = constDecl.getRef();
		return constRefExpr;
	}

	@Override
	public <ReturnType extends Type> Expr<?> visit(final ProcRefExpr<ReturnType> expr, final Integer param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ReturnType extends Type> Expr<?> visit(final ProcCallExpr<ReturnType> expr, final Integer param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
}
