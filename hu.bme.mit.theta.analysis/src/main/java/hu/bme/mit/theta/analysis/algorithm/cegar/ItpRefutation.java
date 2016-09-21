package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public interface ItpRefutation extends Refutation, Iterable<Expr<? extends BoolType>> {

	int size();

	Expr<? extends BoolType> get(int i);
}
