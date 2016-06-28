package hu.bme.mit.inf.ttmc.formalism.common.decl;

import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ClockRefExpr;

public interface ClockDecl extends VarDecl<RatType>, Comparable<ClockDecl> {

	@Override
	public ClockRefExpr getRef();

}
