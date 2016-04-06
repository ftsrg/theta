package hu.bme.mit.inf.ttmc.formalism.common.type;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface ProcType<ReturnType extends Type> extends Type {
	public List<? extends Type> getParamTypes();
	public ReturnType getReturnType();
}
