package hu.bme.mit.theta.core.type.booltype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.MultiaryExpr;
import hu.bme.mit.theta.core.model.Valuation;

public final class OrExpr extends MultiaryExpr<BoolType, BoolType> {

	private static final int HASH_SEED = 131;

	private static final String OPERATOR_LABEL = "Or";

	OrExpr(final Iterable<? extends Expr<BoolType>> ops) {
		super(ops);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Valuation val) {
		for (final Expr<BoolType> op : getOps()) {
			final BoolLitExpr opVal = (BoolLitExpr) op.eval(val);
			if (opVal.getValue()) {
				return True();
			}
		}
		return False();
	}

	@Override
	public OrExpr with(final Iterable<? extends Expr<BoolType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new OrExpr(ops);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof OrExpr) {
			final OrExpr that = (OrExpr) obj;
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
