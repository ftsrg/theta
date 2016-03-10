package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.IntDivExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public class Z3IntDivExpr extends IntDivExprImpl implements Z3Expr<IntType> {
	
	private final Context context;
	
	private volatile com.microsoft.z3.ArithExpr term;

	public Z3IntDivExpr(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp,
			final Context context) {
		super(leftOp, rightOp);
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
