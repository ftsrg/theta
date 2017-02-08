package hu.bme.mit.theta.frontend.c.transform.slicer;

import java.util.Collection;
import java.util.Collections;
import java.util.function.Predicate;

import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.AssertNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;

public interface FunctionSlicer {

	public static final Predicate<IrNode> SLICE_ON_ASSERTS = (IrNode s) -> s instanceof AssertNode;
	
	public default Slice slice(Function function, IrNode criteria) {
		return this.slice(function, criteria, Collections.emptyList());
	}
	
	public Slice slice(Function function, IrNode criteria, Collection<IrNode> additional);
	
}
