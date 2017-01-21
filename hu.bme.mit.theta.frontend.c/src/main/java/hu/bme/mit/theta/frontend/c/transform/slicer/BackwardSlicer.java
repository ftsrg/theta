package hu.bme.mit.theta.frontend.c.transform.slicer;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.frontend.c.dependency.ControlDependencyGraph;
import hu.bme.mit.theta.frontend.c.dependency.UseDefineChain;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.BranchTableNode;
import hu.bme.mit.theta.frontend.c.ir.node.EntryNode;
import hu.bme.mit.theta.frontend.c.ir.node.GotoNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.JumpIfNode;
import hu.bme.mit.theta.frontend.c.ir.node.NodeFactory;
import hu.bme.mit.theta.frontend.c.ir.node.NonTerminatorIrNode;
import hu.bme.mit.theta.frontend.c.ir.node.TerminatorIrNode;

public class BackwardSlicer extends FunctionSlicer {

	@Override
	protected List<IrNode> markRequiredNodes(Function function, IrNode criteria) {
		// Build dependency structures
		// XXX: These structures should be cached, as they are the same for a single allSlice call
		UseDefineChain ud = UseDefineChain.buildChain(function);
		ControlDependencyGraph cdg = ControlDependencyGraph.buildGraph(function);
		
		Queue<IrNode> worklist = new ArrayDeque<>();
		List<IrNode> visited = new ArrayList<>();

		worklist.add(criteria);

		while (!worklist.isEmpty()) {
			IrNode current = worklist.poll();

			if (!visited.contains(current)) {
				visited.add(current);

				Collection<NonTerminatorIrNode> flowDeps = ud.getDefinitions(current).stream()
						.filter(d -> !visited.contains(d)).collect(Collectors.toList());

				Collection<TerminatorIrNode> controlDeps = cdg.getParentBlocks(current.getParentBlock()).stream()
						.map(b -> b.getTerminator()).filter(t -> !visited.contains(t)).collect(Collectors.toList());

				worklist.addAll(flowDeps);
				worklist.addAll(controlDeps);
			}
		}

		return visited;
	}

}
