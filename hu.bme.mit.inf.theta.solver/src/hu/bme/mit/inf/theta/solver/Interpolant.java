package hu.bme.mit.inf.theta.solver;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;

public interface Interpolant {

	public Expr<BoolType> eval(final ItpMarker marker);
	
}
