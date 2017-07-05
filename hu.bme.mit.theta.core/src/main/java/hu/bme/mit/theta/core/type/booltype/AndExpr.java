package hu.bme.mit.theta.core.type.booltype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.MultiaryExpr;
import hu.bme.mit.theta.core.model.Substitution;

public final class AndExpr extends MultiaryExpr<BoolType, BoolType> {

	private static final int HASH_SEED = 41;

	private static final String OPERATOR_LABEL = "And";

	AndExpr(final Iterable<? extends Expr<BoolType>> ops) {
		super(ops);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Substitution assignment) {
		for (final Expr<BoolType> op : getOps()) {
			final BoolLitExpr opVal = (BoolLitExpr) op.eval(assignment);
			if (!opVal.getValue()) {
				return False();
			}
		}
		return True();
	}

	@Override
	public AndExpr with(final Iterable<? extends Expr<BoolType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new AndExpr(ops);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AndExpr) {
			final AndExpr that = (AndExpr) obj;
			return this.getOps().equals(that.getOps());
		} else {
			return false;
		}
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

}
