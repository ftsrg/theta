package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractModExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public class Z3ModExpr extends AbstractModExpr implements Z3Expr<IntType> {

	private final Context context;

	private volatile com.microsoft.z3.IntExpr term;

	public Z3ModExpr(final ConstraintManager manager, final Expr<? extends IntType> leftOp,
			final Expr<? extends IntType> rightOp, final Context context) {
		super(manager, leftOp, rightOp);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.IntExpr getTerm() {
		if (term == null) {
			final Z3Expr<?> leftOp = (Z3Expr<?>) getLeftOp();
			final Z3Expr<?> rightOp = (Z3Expr<?>) getRightOp();
			final com.microsoft.z3.IntExpr leftOpTerm = (com.microsoft.z3.IntExpr) leftOp.getTerm();
			final com.microsoft.z3.IntExpr rightOpTerm = (com.microsoft.z3.IntExpr) rightOp.getTerm();
			term = context.mkMod(leftOpTerm, rightOpTerm);
		}

		return term;
	}

}
