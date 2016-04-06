package hu.bme.mit.inf.ttmc.constraint.solver;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public interface ItpMarker {
	
	public Collection<? extends Expr<? extends BoolType>> getAssertions();
}
