package hu.bme.mit.inf.ttmc.core.solver;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface ItpMarker {
	
	public Collection<? extends Expr<? extends BoolType>> getAssertions();
}
