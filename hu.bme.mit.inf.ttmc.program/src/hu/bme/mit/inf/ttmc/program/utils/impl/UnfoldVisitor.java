package hu.bme.mit.inf.ttmc.program.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprRewriterVisitor;
import hu.bme.mit.inf.ttmc.program.decl.VarDecl;
import hu.bme.mit.inf.ttmc.program.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.program.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.program.utils.ProgExprVisitor;


class UnfoldVisitor extends ExprRewriterVisitor<Integer> implements ProgExprVisitor<Integer, Expr<?>> {

	final VarMap varMap;
	final ExprFactory exprFactory;
	
	UnfoldVisitor(VarMap varMap, ExprFactory exprFactory) {
		this.varMap = varMap;
		this.exprFactory = exprFactory;
	}
		
	////
	
	@Override
	public <ExprType extends Type> Expr<? extends ExprType> visit(PrimedExpr<ExprType> expr, Integer param) {
		final int i = param;
		final Expr<? extends ExprType> op = expr.getOp();
		@SuppressWarnings("unchecked")
		final Expr<? extends ExprType> res = (Expr<? extends ExprType>) op.accept(this, i + 1);
		return res;
	}

	@Override
	public <DeclType extends Type> Expr<? extends DeclType> visit(VarRefExpr<DeclType> expr, Integer param) {
		final int i = param;
		final VarDecl<DeclType> varDecl = expr.getDecl();
		final ConstDecl<DeclType> constDecl =  varMap.getConstDecl(varDecl, i);
		final ConstRefExpr<DeclType> constRefExpr = exprFactory.Ref(constDecl);
		return constRefExpr;
	}

	@Override
	public <ReturnType extends Type> Expr<?> visit(ProcRefExpr<ReturnType> expr, Integer param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ReturnType extends Type> Expr<?> visit(ProcCallExpr<ReturnType> expr, Integer param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
}
