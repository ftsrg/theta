package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeInferrer;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrerImpl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public final class FormalismTypeInferrerImpl extends TypeInferrerImpl implements TypeInferrer {

	private final TypeInferrerVisitor visitor;
	
	public FormalismTypeInferrerImpl(final TypeFactory typeFactory) {
		super(typeFactory);
		visitor = new FormalismTypeInferrerVisitor(typeFactory);
	}
	
	@Override
	public <T extends Type> T getType(final Expr<T> expr) {
		checkNotNull(expr);
		return visitor.getType(expr);
	}

	private static class FormalismTypeInferrerVisitor extends TypeInferrerVisitor implements FormalismExprVisitor<Void, Type> {

		public FormalismTypeInferrerVisitor(final TypeFactory typeFactory) {
			super(typeFactory);
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
