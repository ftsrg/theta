package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.MulExpr;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class IntMulExpr extends MulExpr<IntType> {

	private static final int HASH_SEED = 2707;
	private static final String OPERATOR_LABEL = "Mul";

	IntMulExpr(final Iterable<? extends Expr<IntType>> ops) {
		super(ops);
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntMulExpr withOps(final Iterable<? extends Expr<IntType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new IntMulExpr(ops);
		}
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IntMulExpr) {
			final IntMulExpr that = (IntMulExpr) obj;
			return this.getOps().equals(that.getOps());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
