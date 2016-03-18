package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractIteExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class Z3IteExpr<ExprType extends Type> extends AbstractIteExpr<ExprType> implements Z3Expr<ExprType> {

	private final Context context;

	private volatile com.microsoft.z3.Expr term;

	public Z3IteExpr(final ConstraintManager manager, final Expr<? extends BoolType> cond,
			final Expr<? extends ExprType> then, final Expr<? extends ExprType> elze, final Context context) {
		super(manager, cond, then, elze);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.Expr getTerm() {
		if (term == null) {
			final Z3Expr<?> cond = (Z3Expr<?>) getCond();
			final Z3Expr<?> then = (Z3Expr<?>) getThen();
			final Z3Expr<?> elze = (Z3Expr<?>) getElse();

			final com.microsoft.z3.BoolExpr condTerm = (com.microsoft.z3.BoolExpr) cond.getTerm();
			final com.microsoft.z3.Expr thenTerm = then.getTerm();
			final com.microsoft.z3.Expr elzeTerm = elze.getTerm();
			term = context.mkITE(condTerm, thenTerm, elzeTerm);
		}

		return term;
	}

}
