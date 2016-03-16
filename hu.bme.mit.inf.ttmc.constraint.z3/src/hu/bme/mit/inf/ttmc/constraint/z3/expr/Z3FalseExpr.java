package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractFalseExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public final class Z3FalseExpr extends AbstractFalseExpr implements Z3Expr<BoolType> {

	@SuppressWarnings("unused")
	private final Context context;

	private final com.microsoft.z3.BoolExpr term;

	public Z3FalseExpr(final ConstraintManager manager, final Context context) {
		super(manager);
		this.context = context;
		term = context.mkFalse();
	}

	@Override
	public com.microsoft.z3.BoolExpr getTerm() {
		return term;
	}
}
