package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.EqExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class Z3EqExpr extends EqExprImpl implements Z3Expr<BoolType> {

	private final Context context;
	
	private volatile com.microsoft.z3.BoolExpr term;

	public Z3EqExpr(Expr<? extends Type> leftOp, Expr<? extends Type> rightOp, final Context context) {
		super(leftOp, rightOp);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.BoolExpr getTerm() {
		if (term == null) {
			final Z3Expr<?> leftOp = (Z3Expr<?>) getLeftOp();
			final Z3Expr<?> rightOp = (Z3Expr<?>) getRightOp();
			final com.microsoft.z3.Expr leftOpTerm = leftOp.getTerm();
			final com.microsoft.z3.Expr rightOpTerm = rightOp.getTerm();
			term = context.mkEq(leftOpTerm, rightOpTerm);
		}
		
		return term;
	}

}
