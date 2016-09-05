package hu.bme.mit.inf.theta.formalism.common.type;

import java.util.List;

import hu.bme.mit.inf.theta.core.type.Type;

public interface ProcType<ReturnType extends Type> extends Type {
	public List<? extends Type> getParamTypes();
	public ReturnType getReturnType();
}
