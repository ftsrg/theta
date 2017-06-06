package hu.bme.mit.theta.core.type.booltype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.decl.ParamDecl;

public final class ExistsExpr extends QuantifiedExpr {

	private static final int HASH_SEED = 7993;

	private static final String OPERATOR_LABEL = "Exists";

	ExistsExpr(final Iterable<? extends ParamDecl<?>> paramDecls, final Expr<BoolType> op) {
		super(paramDecls, op);
	}

	@Override
	public ExistsExpr with(final Expr<BoolType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new ExistsExpr(getParamDecls(), op);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ExistsExpr) {
			final ExistsExpr that = (ExistsExpr) obj;
			return this.getParamDecls().equals(that.getParamDecls()) && this.getOp().equals(that.getOp());
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
