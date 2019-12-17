package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntExprs;

/**
 * Utility to fill valuations with uninitialized parameters.
 * Currently this only fills integer variables with zeroes.
 * Probably has no use in real usage.
 */
public class FillValuation {
	private static FillValuation instance;

	private FillValuation() {
	}

	public static FillValuation getInstance() {
		if (instance == null) instance = new FillValuation();
		return instance;
	}

	<DeclType extends Type> void fill(Expr<DeclType> expr, MutableValuation param) {
		for (Decl var : DeclarationCollector.getDecls(expr)) {
			if (!param.getDecls().contains(var)) {
				param.put(var, IntExprs.Int(0));
			}
		}
	}
}
