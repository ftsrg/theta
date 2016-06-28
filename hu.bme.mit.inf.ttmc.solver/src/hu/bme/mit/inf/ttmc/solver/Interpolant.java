package hu.bme.mit.inf.ttmc.solver;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface Interpolant {

	public Expr<BoolType> eval(final ItpMarker marker);
	
}
