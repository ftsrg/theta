package hu.bme.mit.inf.theta.solver;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;

public interface ItpMarker {
	
	public Collection<? extends Expr<? extends BoolType>> getAssertions();
}
