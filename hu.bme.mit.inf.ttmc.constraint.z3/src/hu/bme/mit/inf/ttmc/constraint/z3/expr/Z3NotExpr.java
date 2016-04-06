package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractNotExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class Z3NotExpr extends AbstractNotExpr implements Z3Expr<BoolType> {

	private final Context context;

	private volatile com.microsoft.z3.BoolExpr term;

	public Z3NotExpr(final ConstraintManager manager, final Expr<? extends BoolType> op, final Context context) {
		super(manager, op);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.BoolExpr getTerm() {
		if (term == null) {
			final Z3Expr<?> op = (Z3Expr<?>) getOp();
			final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) op.getTerm();
			term = context.mkNot(opTerm);
		}

		return term;
	}

}
