package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.impl.IntLitExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public final class Z3IntLitExpr extends IntLitExprImpl implements Z3Expr<IntType> {

	private final Context context;
	
	private volatile com.microsoft.z3.IntNum term;
	
	public Z3IntLitExpr(final long value, final Context context) {
		super(value);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.IntNum getTerm() {
		if (term == null) {
			term = context.mkInt(getValue());
		}

		return term;
	}
}