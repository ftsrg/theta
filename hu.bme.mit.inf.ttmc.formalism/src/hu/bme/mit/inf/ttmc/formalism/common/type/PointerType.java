package hu.bme.mit.inf.ttmc.formalism.common.type;

import hu.bme.mit.inf.ttmc.core.type.Type;

public interface PointerType<T extends Type> extends Type {

	public T getType();

}
