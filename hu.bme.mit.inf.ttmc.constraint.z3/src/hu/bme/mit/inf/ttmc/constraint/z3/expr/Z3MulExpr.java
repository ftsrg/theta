package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import java.util.Collection;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.MulExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;

public class Z3MulExpr<ExprType extends ClosedUnderMul> extends MulExprImpl<ExprType> implements Z3Expr<ExprType> {

	private final Context context;

	private volatile com.microsoft.z3.ArithExpr term;

	public Z3MulExpr(final Collection<? extends Expr<? extends ExprType>> ops, final Context context) {
		super(ops);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.ArithExpr getTerm() {
		if (term == null) {
			final com.microsoft.z3.ArithExpr[] opTerms = new com.microsoft.z3.ArithExpr[getOps().size()];
			int i = 0;
			for (Expr<?> op : getOps()) {
				final Z3Expr<?> z3op = (Z3Expr<?>) op;
				opTerms[i] = (com.microsoft.z3.ArithExpr) z3op.getTerm();
				i++;
			}
			term = context.mkMul(opTerms);
		}

		return term;
	}
}
