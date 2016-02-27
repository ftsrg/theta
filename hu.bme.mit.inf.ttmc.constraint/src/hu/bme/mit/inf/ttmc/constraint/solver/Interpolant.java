package hu.bme.mit.inf.ttmc.constraint.solver;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public interface Interpolant {

	public Expr<BoolType> eval(final ItpMarker marker);
	
}
