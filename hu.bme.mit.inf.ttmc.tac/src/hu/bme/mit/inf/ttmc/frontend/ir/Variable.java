package hu.bme.mit.inf.ttmc.frontend.ir;

import hu.bme.mit.inf.ttmc.core.type.Type;

public class Variable<ValueType extends Type> {

	private String name;

	public Variable(String name) {
		this.name = name;
	}


}
