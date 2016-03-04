package hu.bme.mit.inf.ttmc.program.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprIteEliminator;
import hu.bme.mit.inf.ttmc.program.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.program.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.program.utils.ProgExprVisitor;

/**
 * If-Then-Else eliminator.
 * @author Akos
 *
 */
public final class ProgExprIteEliminator extends ExprIteEliminator {
	
	/**
	 * Helper visitor 1
	 * Propagate ITE up in the expression tree as high as possible.
	 * @author Akos
	 */
	private static class PropagateProgIteVisitor extends PropagateIteVisitor implements ProgExprVisitor<Void, Expr<? extends Type>>  {

		public PropagateProgIteVisitor(ConstraintManager manager, ProgExprVisitor<Void, Expr<? extends Type>> pushBelowIteVisitor) {
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
	private static class PushBelowProgIteVisitor extends PushBelowIteVisitor implements ProgExprVisitor<Void, Expr<? extends Type>> {

		public PushBelowProgIteVisitor(ConstraintManager manager) {
			super(manager, new IsBooleanConnectiveProgExprVisitor());
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
	private static class RemoveProgIteVisitor extends RemoveIteVisitor implements ProgExprVisitor<Void, Expr<? extends Type>> {

		public RemoveProgIteVisitor(ConstraintManager manager) {
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
	public ProgExprIteEliminator(ConstraintManager manager) {
		super(manager);
	}
	
	@Override
	protected PropagateIteVisitor getPropageteIteVisitor(ConstraintManager manager) {
		return new PropagateProgIteVisitor(manager, new PushBelowProgIteVisitor(manager));
	}
	
	@Override
	protected RemoveIteVisitor getRemoveIteVisitor(ConstraintManager manager) {
		return new RemoveProgIteVisitor(manager);
	}
}
