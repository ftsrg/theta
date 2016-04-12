package hu.bme.mit.inf.ttmc.solver.impl;


import hu.bme.mit.inf.ttmc.core.type.Type;

public interface WrapperType<Sort> extends Type {

	public Sort getSort();

}
