package hu.bme.mit.inf.theta.frontend.transform;

import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;

public interface ContextTransformer {

	public void transform(GlobalContext context);

	public String getTransformationName();

}
