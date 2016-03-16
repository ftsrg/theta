package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractExistsExpr extends AbstractQuantifiedExpr implements ExistsExpr {

	private static final int HASH_SEED = 7993;

	private static final String OPERATOR_LABEL = "Exists";

	private final ConstraintManager manager;

	public AbstractExistsExpr(final ConstraintManager manager,
			final Collection<? extends ParamDecl<? extends Type>> paramDecls, final Expr<? extends BoolType> op) {
		super(paramDecls, op);
		this.manager = manager;
	}

	@Override
	public final ExistsExpr withOp(final Expr<? extends BoolType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return manager.getExprFactory().Exists(getParamDecls(), op);
		}
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final boolean equals(final Object obj) {
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
	protected final int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected final String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
