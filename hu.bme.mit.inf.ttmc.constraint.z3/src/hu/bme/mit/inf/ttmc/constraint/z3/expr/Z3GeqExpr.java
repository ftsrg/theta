package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractGeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public final class Z3GeqExpr extends AbstractGeqExpr implements Z3Expr<BoolType> {

	private final Context context;

	private volatile com.microsoft.z3.BoolExpr term;

	public Z3GeqExpr(final ConstraintManager manager, final Expr<? extends RatType> leftOp,
			final Expr<? extends RatType> rightOp, final Context context) {
		super(manager, leftOp, rightOp);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.BoolExpr getTerm() {
		if (term == null) {
			final Z3Expr<?> leftOp = (Z3Expr<?>) getLeftOp();
			final Z3Expr<?> rightOp = (Z3Expr<?>) getRightOp();
			final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) leftOp.getTerm();
			final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) rightOp.getTerm();
			term = context.mkGe(leftOpTerm, rightOpTerm);
		}

		return term;
	}

}
