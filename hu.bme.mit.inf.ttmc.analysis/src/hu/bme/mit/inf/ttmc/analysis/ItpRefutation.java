package hu.bme.mit.inf.ttmc.analysis;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface ItpRefutation extends Refutation, Iterable<Expr<? extends BoolType>> {

	int size();

	Expr<? extends BoolType> get(int i);
}
