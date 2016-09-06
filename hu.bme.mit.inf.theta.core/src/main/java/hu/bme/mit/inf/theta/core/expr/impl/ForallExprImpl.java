package hu.bme.mit.inf.theta.core.expr.impl;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.decl.ParamDecl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.ForallExpr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.type.impl.Types;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;

final class ForallExprImpl extends AbstractQuantifiedExpr implements ForallExpr {

	private static final int HASH_SEED = 6871;

	private static final String OPERATOR_LABEL = "Forall";

	ForallExprImpl(final Collection<? extends ParamDecl<? extends Type>> paramDecls,
			final Expr<? extends BoolType> op) {
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
			return Exprs.Forall(getParamDecls(), op);
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
