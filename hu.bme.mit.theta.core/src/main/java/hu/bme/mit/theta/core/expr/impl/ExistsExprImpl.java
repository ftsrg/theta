package hu.bme.mit.theta.core.expr.impl;

import java.util.Collection;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.ExistsExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

final class ExistsExprImpl extends AbstractQuantifiedExpr implements ExistsExpr {

	private static final int HASH_SEED = 7993;

	private static final String OPERATOR_LABEL = "Exists";

	ExistsExprImpl(final Collection<? extends ParamDecl<? extends Type>> paramDecls,
			final Expr<? extends BoolType> op) {
		super(paramDecls, op);
	}

	@Override
	public BoolType getType() {
		return Types.Bool();
	}

	@Override
	public ExistsExpr withOp(final Expr<? extends BoolType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return Exprs.Exists(getParamDecls(), op);
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
