package hu.bme.mit.theta.frontend.c.transform;

import hu.bme.mit.theta.frontend.c.ir.GlobalContext;

public interface Transformer {

	public void transform(GlobalContext context);
	
	public String getTransformationName();
	
}
