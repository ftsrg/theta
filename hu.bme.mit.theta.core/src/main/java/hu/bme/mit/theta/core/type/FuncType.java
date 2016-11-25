package hu.bme.mit.theta.core.type;

public interface FuncType<ParamType extends Type, ResultType extends Type> extends Type {

	ParamType getParamType();

	ResultType getResultType();
}
