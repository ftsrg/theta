package hu.bme.mit.theta.core.type.booltype;

import java.util.Collection;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.QuantifiedExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class ForallExpr extends QuantifiedExpr {

	private static final int HASH_SEED = 6871;

	private static final String OPERATOR_LABEL = "Forall";

	ForallExpr(final Collection<? extends ParamDecl<? extends Type>> paramDecls, final Expr<? extends BoolType> op) {
		super(paramDecls, op);
	}

	@Override
	public BoolType getType() {
		return Types.Bool();
	}

	@Override
	public ForallExpr withOp(final Expr<? extends BoolType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new ForallExpr(getParamDecls(), op);
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
		} else if (obj instanceof ForallExpr) {
			final ForallExpr that = (ForallExpr) obj;
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
