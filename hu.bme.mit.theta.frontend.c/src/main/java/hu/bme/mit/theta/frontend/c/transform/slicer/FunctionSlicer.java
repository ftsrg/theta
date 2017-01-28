package hu.bme.mit.theta.frontend.c.transform.slicer;

import java.util.function.Predicate;

import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.AssertNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;

public interface FunctionSlicer {

	public static final Predicate<IrNode> SLICE_ON_ASSERTS = (IrNode s) -> s instanceof AssertNode;
	
	public Function slice(Function function, IrNode criteria);
	
}
