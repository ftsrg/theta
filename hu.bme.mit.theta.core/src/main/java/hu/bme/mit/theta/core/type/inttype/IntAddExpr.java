package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;

public final class IntAddExpr extends AddExpr<IntType> {

	private static final int HASH_SEED = 5653;
	private static final String OPERATOR_LABEL = "Add";

	IntAddExpr(final Iterable<? extends Expr<IntType>> ops) {
		super(ops);
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntLitExpr eval(final Valuation val) {
		int sum = 0;
		for (final Expr<IntType> op : getOps()) {
			final IntLitExpr opVal = (IntLitExpr) op.eval(val);
			sum += opVal.getValue();
		}
		return Int(sum);
	}

	@Override
	public IntAddExpr with(final Iterable<? extends Expr<IntType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new IntAddExpr(ops);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IntAddExpr) {
			final IntAddExpr that = (IntAddExpr) obj;
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
