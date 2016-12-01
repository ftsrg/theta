package hu.bme.mit.theta.core.type;

import java.util.Optional;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.utils.TypeVisitor;

public interface Type {

	LitExpr<? extends Type> getAny();

	boolean isLeq(Type type);

	Optional<? extends Type> meet(Type type);

	Optional<? extends Type> join(Type type);

	<P, R> R accept(TypeVisitor<? super P, ? extends R> visitor, P param);

}
