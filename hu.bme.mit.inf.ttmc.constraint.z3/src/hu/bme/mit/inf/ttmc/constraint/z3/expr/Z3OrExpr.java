package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import java.util.Collection;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.OrExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class Z3OrExpr extends OrExprImpl implements Z3Expr<BoolType> {

	private final Context context;

	private volatile com.microsoft.z3.BoolExpr term;

	public Z3OrExpr(final Collection<? extends Expr<? extends BoolType>> ops, final Context context) {
		super(ops);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.BoolExpr getTerm() {
		if (term == null) {
			final com.microsoft.z3.BoolExpr[] opTerms = new com.microsoft.z3.BoolExpr[getOps().size()];
			int i = 0;
			for (Expr<?> op : getOps()) {
				final Z3Expr<?> z3op = (Z3Expr<?>) op;
				opTerms[i] = (com.microsoft.z3.BoolExpr) z3op.getTerm();
				i++;
			}
			term = context.mkOr(opTerms);
		}

		return term;
	}

}
