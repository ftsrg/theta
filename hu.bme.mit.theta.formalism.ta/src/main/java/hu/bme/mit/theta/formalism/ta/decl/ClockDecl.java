package hu.bme.mit.theta.formalism.ta.decl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.ta.expr.ClockRefExpr;

public interface ClockDecl extends VarDecl<RatType>, Comparable<ClockDecl> {

	@Override
	ClockRefExpr getRef();

}
