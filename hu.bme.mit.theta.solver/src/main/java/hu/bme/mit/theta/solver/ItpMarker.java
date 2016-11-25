package hu.bme.mit.theta.solver;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public interface ItpMarker {

	Collection<? extends Expr<? extends BoolType>> getAssertions();
}
