package hu.bme.mit.inf.ttmc.program.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.CnfExprChecker;
import hu.bme.mit.inf.ttmc.program.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.program.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.program.utils.ProgExprVisitor;

/**
 * CNF checker to decide if an expression is in conjunctive
 * normal form (CNF).
 * 
 * @author Akos
 */
public final class CnfProgExprChecker extends CnfExprChecker {

	@Override
	protected IsCnfExprVisitor getCnfExprVisitor() {
		return new IsCnfProgExprVisitor();
	}
	
	/**
	 * Helper visitor for checking if an expression is in CNF.
	 * @author Akos
	 */
	private class IsCnfProgExprVisitor extends IsCnfExprVisitor implements ProgExprVisitor<Status, Boolean> {

		@Override
		public <ExprType extends Type> Boolean visit(PrimedExpr<ExprType> expr, Status param) {
			// A prime counts as a NOT expression, no boolean connective can be inside it
			return expr.getOp().accept(this, Status.NOT);
		}

		@Override
		public <DeclType extends Type> Boolean visit(VarRefExpr<DeclType> expr, Status param) {
			return true;
		}

		@Override
		public <ReturnType extends Type> Boolean visit(ProcRefExpr<ReturnType> expr, Status param) {
			return true;
		}

		@Override
		public <ReturnType extends Type> Boolean visit(ProcCallExpr<ReturnType> expr, Status param) {
			return true;
		}
		
	}
}
