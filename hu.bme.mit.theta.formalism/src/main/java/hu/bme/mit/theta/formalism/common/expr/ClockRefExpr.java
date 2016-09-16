package hu.bme.mit.theta.formalism.common.expr;

import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;

public interface ClockRefExpr extends VarRefExpr<RatType> {

	@Override
	public ClockDecl getDecl();

}
