package hu.bme.mit.inf.ttmc.formalism.common.expr;

import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public interface ClockRefExpr extends VarRefExpr<RatType> {

	@Override
	public ClockDecl getDecl();

}
