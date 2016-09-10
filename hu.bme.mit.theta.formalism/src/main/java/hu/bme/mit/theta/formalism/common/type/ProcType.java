package hu.bme.mit.theta.formalism.common.type;

import java.util.List;

import hu.bme.mit.theta.core.type.Type;

public interface ProcType<ReturnType extends Type> extends Type {
	public List<? extends Type> getParamTypes();
	public ReturnType getReturnType();
}
