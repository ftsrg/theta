package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractIntDivExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public final class Z3IntDivExpr extends AbstractIntDivExpr implements Z3Expr<IntType> {

	private final Context context;

	private volatile com.microsoft.z3.ArithExpr term;

	public Z3IntDivExpr(final ConstraintManager manager, final Expr<? extends IntType> leftOp,
			final Expr<? extends IntType> rightOp, final Context context) {
		super(manager, leftOp, rightOp);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.ArithExpr getTerm() {
		if (term == null) {
			final Z3Expr<?> leftOp = (Z3Expr<?>) getLeftOp();
			final Z3Expr<?> rightOp = (Z3Expr<?>) getRightOp();
			final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) leftOp.getTerm();
			final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) rightOp.getTerm();
			term = context.mkDiv(leftOpTerm, rightOpTerm);
		}

		return term;
	}

}
