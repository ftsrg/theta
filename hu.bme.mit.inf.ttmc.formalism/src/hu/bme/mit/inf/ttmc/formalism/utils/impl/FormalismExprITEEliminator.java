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

/**
 * If-Then-Else eliminator.
 * @author Akos
 *
 */
public final class FormalismExprITEEliminator extends ExprITEEliminator {
	
	/**
	 * Helper visitor 1
	 * Propagate ITE up in the expression tree as high as possible.
	 * @author Akos
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
	 * Helper visitor 2
	 * Push an expression below an ITE recursively.
	 * @author Akos
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
	 * Helper visitor 3
	 * 
	 * Remove if-then-else expressions by transforming them with the following rule:
	 * (if A then B else C) <=> (!A or B) and (A or C).
	 * 
	 * It is assumed that ite expressions are propagated to the top.
	 * @author Akos
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
	
	/**
	 * Constructor.
	 * @param manager Constraint manager
	 */
	public FormalismExprITEEliminator(ConstraintManager manager) {
		super(manager);
	}
	
	@Override
	protected PropagateITEVisitor getPropageteITEVisitor(ConstraintManager manager) {
		return new PropagateFormalismITEVisitor(manager, new PushBelowFormalismITEVisitor(manager));
	}
	
	@Override
	protected RemoveITEVisitor getRemoveITEVisitor(ConstraintManager manager) {
		return new RemoveFormalismITEVisitor(manager);
	}
}
