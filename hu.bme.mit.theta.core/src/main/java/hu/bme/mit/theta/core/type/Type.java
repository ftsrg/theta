package hu.bme.mit.theta.core.type;

import java.util.Optional;

import hu.bme.mit.theta.core.expr.LitExpr;

public interface Type {

	LitExpr<? extends Type> getAny();

	boolean isLeq(Type type);

	Optional<? extends Type> meet(Type type);

	Optional<? extends Type> join(Type type);

}
