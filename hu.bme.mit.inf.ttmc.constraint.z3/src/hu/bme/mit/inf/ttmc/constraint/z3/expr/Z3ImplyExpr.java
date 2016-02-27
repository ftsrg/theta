package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ImplyExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class Z3ImplyExpr extends ImplyExprImpl implements Z3Expr<BoolType> {

	private final Context context;
	
	private volatile com.microsoft.z3.BoolExpr term;

	public Z3ImplyExpr(Expr<? extends BoolType> leftOp, Expr<? extends BoolType> rightOp,
			final Context context) {
		super(leftOp, rightOp);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.BoolExpr getTerm() {
		if (term == null) {
			final Z3Expr<?> leftOp = (Z3Expr<?>) getLeftOp();
			final Z3Expr<?> rightOp = (Z3Expr<?>) getRightOp();
			final com.microsoft.z3.BoolExpr leftOpTerm = (com.microsoft.z3.BoolExpr) leftOp.getTerm();
			final com.microsoft.z3.BoolExpr rightOpTerm = (com.microsoft.z3.BoolExpr) rightOp.getTerm();
			term = context.mkImplies(leftOpTerm, rightOpTerm);
		}
		
		return term;
	}

}
