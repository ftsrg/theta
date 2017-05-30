package hu.bme.mit.theta.core.type.booltype;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class OrExpr extends MultiaryExpr<BoolType, BoolType> {

	private static final int HASH_SEED = 131;

	private static final String OPERATOR_LABEL = "Or";

	OrExpr(final Collection<? extends Expr<? extends BoolType>> ops) {
		super(ops);
	}

	@Override
	public BoolType getType() {
		return Types.Bool();
	}

	@Override
	public OrExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new OrExpr(ops);
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
