package hu.bme.mit.theta.frontend.c.transform.slicer;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.Queue;

import hu.bme.mit.theta.frontend.c.dependency.ControlDependencyGraph;
import hu.bme.mit.theta.frontend.c.dependency.DominatorTree;
import hu.bme.mit.theta.frontend.c.dependency.UseDefineChain;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;

public class ValueSlicer extends FunctionSlicer {

	@Override
	protected List<IrNode> markRequiredNodes(Function function, IrNode criteria) {
		// Build required dependencies
		UseDefineChain ud = UseDefineChain.buildChain(function);
		ControlDependencyGraph cdg = ControlDependencyGraph.buildGraph(function);
		DominatorTree dt = DominatorTree.createDominatorTree(function);
		
		List<IrNode> vi = new ArrayList<>();
		
		// initialize the worklist with the reaching definitions of the criteria node
		Queue<IrNode> worklist = new ArrayDeque<IrNode>(ud.getDefinitions(criteria));
		
		while (!worklist.isEmpty()) {
			IrNode current = worklist.poll();
			
			vi.add(current);
		}
		
		return vi;
	}
	

	

}
