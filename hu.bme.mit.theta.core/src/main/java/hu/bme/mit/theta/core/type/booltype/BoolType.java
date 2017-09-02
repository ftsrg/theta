package hu.bme.mit.theta.core.type.booltype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;

public final class BoolType implements Equational<BoolType> {

	private static final BoolType INSTANCE = new BoolType();
	private static final int HASH_SEED = 754364;
	private static final String TYPE_LABEL = "Bool";

	private BoolType() {
	}

	static BoolType getInstance() {
		return INSTANCE;
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof BoolType;
	}

	@Override
	public String toString() {
		return TYPE_LABEL;
	}

	////

	@Override
	public IffExpr Eq(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		return BoolExprs.Iff(leftOp, rightOp);
	}

	@Override
	public NeqExpr<BoolType> Neq(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		return BoolExprs.Xor(leftOp, rightOp);
	}

}
