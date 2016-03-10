package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.NeqExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class Z3NeqExpr extends NeqExprImpl implements Z3Expr<BoolType> {

private final Context context;
	
	private volatile com.microsoft.z3.BoolExpr term;

	public Z3NeqExpr(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp, final Context context) {
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
			term = context.mkNot(context.mkEq(leftOpTerm, rightOpTerm));
		}
		
		return term;
	}

}
