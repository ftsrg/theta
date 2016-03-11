package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractRatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public class Z3RatLitExpr extends AbstractRatLitExpr implements Z3Expr<RatType> {

	private final Context context;

	private volatile com.microsoft.z3.RatNum term;

	public Z3RatLitExpr(final long num, final long denom, final Context context) {
		super(num, denom);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.RatNum getTerm() {
		if (term == null) {
			term = context.mkReal(Math.toIntExact(getNum()), Math.toIntExact(getDenom()));
		}

		return term;
	}
}
