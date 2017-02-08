package hu.bme.mit.theta.frontend.c.transform.slicer;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.decl.impl.Decls;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.frontend.c.dependency.ControlDependencyGraph;
import hu.bme.mit.theta.frontend.c.dependency.UseDefineChain;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.BranchTableNode;
import hu.bme.mit.theta.frontend.c.ir.node.ConditionalTerminatorNode;
import hu.bme.mit.theta.frontend.c.ir.node.EntryNode;
import hu.bme.mit.theta.frontend.c.ir.node.GotoNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.JumpIfNode;
import hu.bme.mit.theta.frontend.c.ir.node.NodeFactory;
import hu.bme.mit.theta.frontend.c.ir.node.TerminatorIrNode;
import hu.bme.mit.theta.frontend.c.transform.slicer.Slice.SliceBuilder;
import hu.bme.mit.theta.frontend.c.transform.slicer.utils.SliceCreator;

public class ThinSlicer implements FunctionSlicer {

	@Override
	public Slice slice(Function function, IrNode criteria, Collection<IrNode> additional) {		
		SliceBuilder builder = Slice.builder(function, criteria);
		builder.addAdditional(additional);
		
		// Build the dependency structures
		UseDefineChain ud = UseDefineChain.buildChain(function);
		ControlDependencyGraph cdg = ControlDependencyGraph.buildGraph(function);
		
		List<IrNode> dataDeps = new ArrayList<>();
		
		Queue<IrNode> wl = new ArrayDeque<>();
		wl.add(criteria);
		wl.addAll(additional);
		
		// Find the all nodes which the criteria transitively flow depends on
		// These nodes must be included in the slice as they define the values of the criteria variables
		while (!wl.isEmpty()) {
			IrNode current = wl.poll();
			if (!dataDeps.contains(current)) {
				dataDeps.add(current);
				ud.getDefinitions(current).forEach(node -> {
					wl.add(node);
				});
			}
		}
		
		//dataDeps.forEach(dep -> System.out.println(dep.toString()));
		
		// Find required control dependencies
		List<IrNode> controlDeps = new ArrayList<>();
		
		wl.addAll(dataDeps);
		while (!wl.isEmpty()) {
			IrNode current = wl.poll();
			if (!controlDeps.contains(current)) {
				if (!dataDeps.contains(current))
					controlDeps.add(current);
				
				cdg.getParentBlocks(current.getParentBlock()).stream().map(block -> block.getTerminator()).forEach(terminator -> {
					wl.add(terminator);
				});
			}			
		}

		//controlDeps.forEach(dep -> System.out.println(dep.toString()));
		
		List<IrNode> visited = new ArrayList<>();
		visited.addAll(controlDeps);
		visited.addAll(dataDeps);
		
		builder.setVisited(visited);
		
		Map<BasicBlock, BasicBlock> blockMap = new HashMap<>();
		Function copy = function.copy(blockMap);
		
		builder.setCopy(copy, blockMap);
		
		int brId = 0;
		
		for (Entry<BasicBlock, BasicBlock> entry : blockMap.entrySet()) {
			BasicBlock oldBlock = entry.getKey();
			BasicBlock newBlock = entry.getValue();
			
			TerminatorIrNode terminator = oldBlock.getTerminator();
			if (controlDeps.contains(terminator)) {
				// This is may be a branching node which need to be abstracted
				if (terminator instanceof JumpIfNode) {
					JumpIfNode branch = (JumpIfNode) newBlock.getTerminator();
					
					// Create a new temporary variable to represent a nondeterministic branch
					VarDecl<?> brTmp = Decls.Var("__abr" + (brId++) + "__", Types.Int());
					Expr<? extends BoolType> brCond = Exprs.Neq(brTmp.getRef(), Exprs.Int(0));
					
					branch.setCondition(brCond);
					
					builder.addAbstractPredicate((ConditionalTerminatorNode) terminator, branch);
				}
			}
		}
		
		
		return builder.build();
	}
}
