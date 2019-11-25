package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntExprs;

/**
 * Three types of variables:
 * global
 * process local
 * procedure local with parameters -> can have multiple active instances (in the stack)
 * procedures shall store how many calls have they made
 */

public class FillValuation {
	static FillValuation instance;

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
