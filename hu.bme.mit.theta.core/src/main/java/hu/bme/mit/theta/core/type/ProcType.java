package hu.bme.mit.theta.core.type;

import java.util.List;

public interface ProcType<ReturnType extends Type> extends Type {

	public List<? extends Type> getParamTypes();

	public ReturnType getReturnType();

}
