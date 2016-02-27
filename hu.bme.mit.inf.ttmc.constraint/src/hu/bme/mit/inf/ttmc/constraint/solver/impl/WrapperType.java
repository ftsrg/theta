package hu.bme.mit.inf.ttmc.constraint.solver.impl;


import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface WrapperType<Sort> extends Type {

	public Sort getSort();

}
