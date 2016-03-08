package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrer;
import hu.bme.mit.inf.ttmc.formalism.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public final class FormalismTypeInferrer extends TypeInferrer {

	public FormalismTypeInferrer(ConstraintManager manager) {
		super(manager);
	}
	
	@Override
	protected TypeInferrerVisitor getTypeInferrer(ConstraintManager manager) {
		return new FormalismTypeInferrerVisitor(manager);
	}
	
	private final class FormalismTypeInferrerVisitor extends TypeInferrerVisitor implements FormalismExprVisitor<Void, Type> {

		public FormalismTypeInferrerVisitor(ConstraintManager manager) {
			super(manager);
		}

		@Override
		public <ExprType extends Type> Type visit(PrimedExpr<ExprType> expr, Void param) {
			final Expr<? extends ExprType> op = expr.getOp();
			final ExprType opType = getType(op);
			return opType;
		}

		@Override
		public <ReturnType extends Type> Type visit(ProcCallExpr<ReturnType> expr, Void param) {
			throw new UnsupportedOperationException("TODO");
		}

		@Override
		public <ReturnType extends Type> Type visit(ProcRefExpr<ReturnType> expr, Void param) {
			throw new UnsupportedOperationException("TODO");
		}

		@Override
		public <DeclType extends Type> Type visit(VarRefExpr<DeclType> expr, Void param) {
			return expr.getDecl().getType();
		}
		
	}

}
