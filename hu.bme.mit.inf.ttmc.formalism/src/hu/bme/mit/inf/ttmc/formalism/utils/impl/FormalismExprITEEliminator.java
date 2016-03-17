package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprITEPropagatorVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprITEPusherVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprITERemoverVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public final class FormalismExprITEEliminator {
	ConstraintManager manager;
	
	public FormalismExprITEEliminator(ConstraintManager manager) {
		this.manager = manager;
	}
	
	@SuppressWarnings("unchecked")
	public Expr<? extends BoolType> eliminate(Expr<? extends BoolType> expr) {
		return (Expr<? extends BoolType>) expr.accept(
				new FormalismITEPropagatorVisitor(manager,
						new FormalismITEPusherVisitor(manager)), null).accept(
								new FormalismITERemoverVisitor(manager), null);
	}

	/**
	 * Helper visitor 1: Propagate ITE up in the expression tree as high as possible.
	 * For example: x = 1 + ite(c, t, e) --> ite(c, x = 1 + t, x = 1 + e)
	 */
	private static class FormalismITEPropagatorVisitor extends ExprITEPropagatorVisitor implements FormalismExprVisitor<Void, Expr<? extends Type>>  {

		public FormalismITEPropagatorVisitor(ConstraintManager manager, FormalismExprVisitor<Void, Expr<? extends Type>> formalismITEPusherVisitor) {
			super(manager, formalismITEPusherVisitor);
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
	
	/**
	 * Helper visitor 2: Push an expression below an ITE recursively.
	 * For example: x = ite (c1, ite(c2, t, e1), e2) --> ite(c1, ite(c2, x = t, x = e1), x = e2)
	 */
	private static class FormalismITEPusherVisitor extends ExprITEPusherVisitor implements FormalismExprVisitor<Void, Expr<? extends Type>> {

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

	/**
	 * Helper visitor 3: Replace if-then-else expressions with boolean connectives.
	 * For example: (if A then B else C) <=> (!A or B) and (A or C).
	 * 
	 * It is assumed that ite expressions are propagated as high as possible.
	 */
	private static class FormalismITERemoverVisitor extends ExprITERemoverVisitor implements FormalismExprVisitor<Void, Expr<? extends Type>> {

		public FormalismITERemoverVisitor(ConstraintManager manager) {
			super(manager);
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
	
}
