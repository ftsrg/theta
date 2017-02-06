package hu.bme.mit.theta.frontend.c.transform.slicer;

import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;

public class Slice {

	private Function original;
	private Function sliced;
	
	private IrNode criterion;
	
	private FunctionSlicer refinementSlicer = new BackwardSlicer();
	
	private Slice(Function function, Function sliced, IrNode criterion) {
		this.original = function;
		this.sliced = sliced;
		this.criterion = criterion;
	}
	
	public void refine() {
		// Currently we just refine by including the whole backward slice
		this.sliced = this.refinementSlicer.slice(this.original, this.criterion);
	}
	
	public static Slice create(Function function, IrNode criterion, FunctionSlicer slicer) {
		Function sliced = slicer.slice(function, criterion);
	
		return new Slice(function, sliced, criterion);
	}
	
}

