package hu.bme.mit.theta.formalism.common.type;

import hu.bme.mit.theta.core.Type;

public interface PointerType<PointedType extends Type> extends Type {

	PointedType getPointedType();

}
