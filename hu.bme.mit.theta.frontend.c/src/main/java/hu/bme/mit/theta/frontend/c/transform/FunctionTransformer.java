package hu.bme.mit.theta.frontend.c.transform;

import hu.bme.mit.theta.frontend.c.ir.Function;

public interface FunctionTransformer {

	public void transform(Function function);

	public String getTransformationName();

}
