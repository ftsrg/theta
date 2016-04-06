package hu.bme.mit.inf.ttmc.constraint.z3.solver;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.z3.trasform.Z3TermTransformer;

public class Z3TermWrapper2 implements Z3TermWrapper {

	final ConstraintManager manager;
	final Context context;
	final Z3TermTransformer transformer;

	public Z3TermWrapper2(final ConstraintManager manager, final Context context, final Z3SymbolWrapper symbolWrapper) {
		this.manager = manager;
		this.context = context;
		transformer = new Z3TermTransformer(manager.getExprFactory(), symbolWrapper);
	}

	@Override
	public Expr<?> wrap(final com.microsoft.z3.Expr term) {
		return transformer.toExpr(term);
	}

}
