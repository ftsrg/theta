package hu.bme.mit.inf.ttmc.constraint.type;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;

public interface Type {

	public Expr<? extends Type> getAny();

	public boolean isLeq(Type type);

	public Optional<? extends Type> meet(Type type);

	public Optional<? extends Type> join(Type type);

	public <P, R> R accept(TypeVisitor<? super P, ? extends R> visitor, P param);

}
