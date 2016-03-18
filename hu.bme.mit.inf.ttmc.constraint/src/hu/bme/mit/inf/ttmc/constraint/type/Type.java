package hu.bme.mit.inf.ttmc.constraint.type;

import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;

public interface Type {

	public boolean isLeq(Type type);

	public <P, R> R accept(TypeVisitor<? super P, ? extends R> visitor, P param);

}
