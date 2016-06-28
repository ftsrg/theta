package hu.bme.mit.inf.ttmc.formalism.common.type;

import hu.bme.mit.inf.ttmc.core.type.Type;

public interface PointerType<PointedType extends Type> extends Type {

	public PointedType getPointedType();

}
