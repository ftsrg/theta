package hu.bme.mit.theta.frontend.c.transform;

import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.GlobalContext;

abstract public class FunctionTransformer implements Transformer {

	@Override
	public void transform(GlobalContext context) {
		for (Function function : context.functions()) {
			this.transform(function);
		}
	}
	
	abstract public void transform(Function function);

	abstract public String getTransformationName();

}
