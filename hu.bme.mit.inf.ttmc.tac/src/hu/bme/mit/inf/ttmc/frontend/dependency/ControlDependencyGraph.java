package hu.bme.mit.inf.ttmc.frontend.dependency;

import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;

public class ControlDependencyGraph {

	private DominatorTree pdt;
	private Function function;

	public ControlDependencyGraph(Function function) {
		this.pdt = DominatorTree.createPostDominatorTree(function);
		this.function = function;
	}

}
