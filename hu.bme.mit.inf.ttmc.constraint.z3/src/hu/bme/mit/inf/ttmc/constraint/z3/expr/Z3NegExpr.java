package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractNegExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;

public class Z3NegExpr<ExprType extends ClosedUnderNeg> extends AbstractNegExpr<ExprType> implements Z3Expr<ExprType> {

	private final Context context;

	private volatile com.microsoft.z3.ArithExpr term;

	public Z3NegExpr(final Expr<? extends ExprType> op, final Context context) {
		super(op);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.ArithExpr getTerm() {
		if (term == null) {
			final Z3Expr<?> op = (Z3Expr<?>) getOp();
			final com.microsoft.z3.ArithExpr opTerm = (com.microsoft.z3.ArithExpr) op.getTerm();
			term = context.mkUnaryMinus(opTerm);
		}

		return term;
	}

}
