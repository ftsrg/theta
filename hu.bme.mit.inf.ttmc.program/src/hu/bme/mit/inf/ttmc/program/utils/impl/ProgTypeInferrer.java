package hu.bme.mit.inf.ttmc.program.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrer;
import hu.bme.mit.inf.ttmc.program.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.program.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.program.utils.AllExprVisitor;

public final class ProgTypeInferrer extends TypeInferrer {

	public ProgTypeInferrer(ConstraintManager manager) {
		super(manager);
	}
	
	@Override
	protected TypeInferrerVisitor getTypeInferrer(ConstraintManager manager) {
		return new ProgTypeInferrerVisitor(manager);
	}
	
	private final class ProgTypeInferrerVisitor extends TypeInferrerVisitor implements AllExprVisitor<Void, Type> {

		public ProgTypeInferrerVisitor(ConstraintManager manager) {
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
