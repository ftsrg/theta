package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprITEEliminator;
import hu.bme.mit.inf.ttmc.formalism.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public final class FormalismExprITEEliminator extends ExprITEEliminator {
	
	public FormalismExprITEEliminator(ConstraintManager manager) {
		super(manager);
	}
	
	// Provide own visitor that supports all formalism expressions
	@Override
	protected PropagateITEVisitor getPropageteITEVisitor(ConstraintManager manager) {
		return new PropagateFormalismITEVisitor(manager, new PushBelowFormalismITEVisitor(manager));
	}

	// Provide own visitor that supports all formalism expressions
	@Override
	protected RemoveITEVisitor getRemoveITEVisitor(ConstraintManager manager) {
		return new RemoveFormalismITEVisitor(manager);
	}
	
	/**
	 * Helper visitor 1: Propagate ITE up in the expression tree as high as possible.
	 * For example: x = 1 + ite(c, t, e) --> ite(c, x = 1 + t, x = 1 + e)
	 */
	private static class PropagateFormalismITEVisitor extends PropagateITEVisitor implements FormalismExprVisitor<Void, Expr<? extends Type>>  {

		public PropagateFormalismITEVisitor(ConstraintManager manager, FormalismExprVisitor<Void, Expr<? extends Type>> pushBelowIteVisitor) {
			super(manager, pushBelowIteVisitor);
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
	private static class PushBelowFormalismITEVisitor extends PushBelowITEVisitor implements FormalismExprVisitor<Void, Expr<? extends Type>> {

		public PushBelowFormalismITEVisitor(ConstraintManager manager) {
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
	private static class RemoveFormalismITEVisitor extends RemoveITEVisitor implements FormalismExprVisitor<Void, Expr<? extends Type>> {

		public RemoveFormalismITEVisitor(ConstraintManager manager) {
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
