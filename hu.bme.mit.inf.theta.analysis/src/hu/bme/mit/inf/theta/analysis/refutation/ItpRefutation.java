package hu.bme.mit.inf.theta.analysis.refutation;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;

public interface ItpRefutation extends Refutation, Iterable<Expr<? extends BoolType>> {

	int size();

	Expr<? extends BoolType> get(int i);
}
