package hu.bme.mit.inf.ttmc.program.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ite.PropagateIteVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ite.PushBelowIteVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ite.RemoveIteVisitor;
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
public class ProgExprIteEliminator {
	
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

	private PropagateProgIteVisitor propagateProgIteVisitor;
	private RemoveProgIteVisitor removeProgIteVisitor;
	
	/**
	 * Constructor.
	 * @param manager Constraint manager
	 */
	public ProgExprIteEliminator(ConstraintManager manager) {
		propagateProgIteVisitor = new PropagateProgIteVisitor(manager, new PushBelowProgIteVisitor(manager));
		removeProgIteVisitor = new RemoveProgIteVisitor(manager);
	}
	
	/**
	 * Eliminate if-then-else expressions by replacing them with boolean connectives.
	 * @param expr Expression from where ITE has to be eliminated
	 * @return New expression with no ITE
	 */
	@SuppressWarnings("unchecked")
	public Expr<? extends BoolType> eliminate(Expr<? extends BoolType> expr) {
		return (Expr<? extends BoolType>) expr.accept(propagateProgIteVisitor, null).accept(removeProgIteVisitor, null);
	}
}
