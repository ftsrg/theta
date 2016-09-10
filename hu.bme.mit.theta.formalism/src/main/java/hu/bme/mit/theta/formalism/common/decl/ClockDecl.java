package hu.bme.mit.theta.formalism.common.decl;

import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.common.expr.ClockRefExpr;

public interface ClockDecl extends VarDecl<RatType>, Comparable<ClockDecl> {

	@Override
	public ClockRefExpr getRef();

}
