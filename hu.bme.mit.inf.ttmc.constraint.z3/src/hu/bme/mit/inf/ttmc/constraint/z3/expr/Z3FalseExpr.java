package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.impl.FalseExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class Z3FalseExpr extends FalseExprImpl implements Z3Expr<BoolType> {
	
	@SuppressWarnings("unused")
	private final Context context;
	
	private final com.microsoft.z3.BoolExpr term;
	
	public Z3FalseExpr(final Context context) {
		this.context = context;
		term = context.mkFalse();
	}

	@Override
	public com.microsoft.z3.BoolExpr getTerm() {
		return term;
	}
}
