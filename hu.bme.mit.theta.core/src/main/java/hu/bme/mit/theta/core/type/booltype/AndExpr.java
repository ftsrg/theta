package hu.bme.mit.theta.core.type.booltype;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class AndExpr extends MultiaryExpr<BoolType, BoolType> {

	private static final int HASH_SEED = 41;

	private static final String OPERATOR_LABEL = "And";

	AndExpr(final Collection<? extends Expr<? extends BoolType>> ops) {
		super(ops);
	}

	@Override
	public BoolType getType() {
		return Types.Bool();
	}

	@Override
	public AndExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new AndExpr(ops);
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
