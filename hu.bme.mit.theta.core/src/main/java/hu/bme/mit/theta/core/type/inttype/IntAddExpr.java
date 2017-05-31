package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.Types.Int;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class IntAddExpr extends AddExpr<IntType> {

	private static final int HASH_SEED = 5653;
	private static final String OPERATOR_LABEL = "Add";

	IntAddExpr(final Collection<? extends Expr<? extends IntType>> ops) {
		super(ops);
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntAddExpr withOps(final Collection<? extends Expr<? extends IntType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new IntAddExpr(ops);
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
