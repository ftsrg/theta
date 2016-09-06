package hu.bme.mit.inf.theta.formalism.common.expr;

import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;

public interface ClockRefExpr extends VarRefExpr<RatType> {

	@Override
	public ClockDecl getDecl();

}
