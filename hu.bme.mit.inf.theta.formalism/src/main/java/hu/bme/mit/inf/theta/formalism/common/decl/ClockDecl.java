package hu.bme.mit.inf.theta.formalism.common.decl;

import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.formalism.common.expr.ClockRefExpr;

public interface ClockDecl extends VarDecl<RatType>, Comparable<ClockDecl> {

	@Override
	public ClockRefExpr getRef();

}
