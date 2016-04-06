package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import java.util.Collection;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractOrExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class Z3OrExpr extends AbstractOrExpr implements Z3Expr<BoolType> {

	private final Context context;

	private volatile com.microsoft.z3.BoolExpr term;

	public Z3OrExpr(final ConstraintManager manager, final Collection<? extends Expr<? extends BoolType>> ops,
			final Context context) {
		super(manager, ops);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.BoolExpr getTerm() {
		if (term == null) {
			final com.microsoft.z3.BoolExpr[] opTerms = new com.microsoft.z3.BoolExpr[getOps().size()];
			int i = 0;
			for (final Expr<?> op : getOps()) {
				final Z3Expr<?> z3op = (Z3Expr<?>) op;
				opTerms[i] = (com.microsoft.z3.BoolExpr) z3op.getTerm();
				i++;
			}
			term = context.mkOr(opTerms);
		}

		return term;
	}

}
