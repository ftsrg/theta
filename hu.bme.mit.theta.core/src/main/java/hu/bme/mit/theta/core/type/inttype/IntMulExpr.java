package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;

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
	public IntLitExpr eval(final Valuation val) {
		int prod = 1;
		for (final Expr<IntType> op : getOps()) {
			final IntLitExpr opVal = (IntLitExpr) op.eval(val);
			prod *= opVal.getValue();
		}
		return Int(prod);
	}

	@Override
	public IntMulExpr with(final Iterable<? extends Expr<IntType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new IntMulExpr(ops);
		}
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
