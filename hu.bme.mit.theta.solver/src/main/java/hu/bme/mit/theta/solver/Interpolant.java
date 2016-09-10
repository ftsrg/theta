package hu.bme.mit.theta.solver;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public interface Interpolant {

	public Expr<BoolType> eval(final ItpMarker marker);
	
}
