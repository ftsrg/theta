package hu.bme.mit.inf.ttmc.program.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.program.expr.PrimedExpr;

public final class PrimedExprImpl<ExprType extends Type> implements PrimedExpr<ExprType> {

	private final static int HASHSEED = 317;
	private volatile int hashCode = 0;
	
	private final Expr<? extends ExprType> op;
	
	public PrimedExprImpl(final Expr<? extends ExprType> op) {
		this.op = op;
	}

	@Override
	public Expr<? extends ExprType> getOp() {
		return op;
	}

	@Override
	public UnaryExpr<ExprType, ExprType> withOp(Expr<? extends ExprType> op) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 37 * hashCode + getOp().hashCode();
		}

		return hashCode;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(op.toString());
		sb.append(")'");
		return sb.toString();
	}
}
