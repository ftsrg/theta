package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractForallExpr extends AbstractQuantifiedExpr implements ForallExpr {

	private static final int HASH_SEED = 6871;

	private static final String OPERATOR_LABEL = "Forall";

	private final ConstraintManager manager;

	public AbstractForallExpr(final ConstraintManager manager,
			final Collection<? extends ParamDecl<? extends Type>> paramDecls, final Expr<? extends BoolType> op) {
		super(paramDecls, op);
		this.manager = manager;
	}

	@Override
	public final BoolType getType() {
		return manager.getTypeFactory().Bool();
	}

	@Override
	public ForallExpr withOp(final Expr<? extends BoolType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return manager.getExprFactory().Forall(getParamDecls(), op);
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
		} else if (obj instanceof ForallExpr) {
			final ForallExpr that = (ForallExpr) obj;
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
