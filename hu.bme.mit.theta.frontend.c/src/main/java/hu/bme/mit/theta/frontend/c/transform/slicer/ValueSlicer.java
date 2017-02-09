package hu.bme.mit.theta.frontend.c.transform.slicer;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Stack;
import java.util.stream.Collectors;

import com.google.common.collect.Multimap;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.decl.impl.Decls;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.frontend.c.dependency.ControlDependencyGraph;
import hu.bme.mit.theta.frontend.c.dependency.ControlDependencyGraph.CDGNode;
import hu.bme.mit.theta.frontend.c.dependency.UseDefineChain;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.ConditionalTerminatorNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.JumpIfNode;
import hu.bme.mit.theta.frontend.c.ir.node.TerminatorIrNode;
import hu.bme.mit.theta.frontend.c.ir.utils.CfgEdge;
import hu.bme.mit.theta.frontend.c.transform.slicer.Slice.SliceBuilder;
import hu.bme.mit.theta.frontend.c.transform.slicer.utils.SliceCreator;

public class ValueSlicer implements FunctionSlicer {

	@Override
	public Slice slice(Function function, IrNode criteria, Collection<IrNode> additional) {
		SliceBuilder builder = Slice.builder(function, criteria);
		builder.addAdditional(additional);
		
		// Build the dependency structures
		UseDefineChain ud = UseDefineChain.buildChain(function);
		ControlDependencyGraph cdg = ControlDependencyGraph.buildGraph(function);
		
		CDGNode critCdg = cdg.getNode(criteria.getParentBlock());
		

		// Store all nodes on which the criteria node transitively control depends
		Multimap<CDGNode, CfgEdge> lcd = cdg.cdgPredecessors(critCdg);
		List<IrNode> tcd = lcd.keySet().stream().map(k -> k.block.getTerminator()).collect(Collectors.toList());
				List<IrNode> vi = new ArrayList<>();
		
		Queue<IrNode> wl = new ArrayDeque<>();
		wl.add(criteria);
		wl.addAll(additional);
		
		// Find value-impacting nodes
		while (!wl.isEmpty()) {
			IrNode current = wl.poll();
			if (!vi.contains(current)) {
				vi.add(current);
				// Nodes on which a value-impacting node flow depends are value-impacting as well
				ud.getDefinitions(current).forEach(node -> {
					wl.add(node);
				});
				
				// Find nodes which are value-impacting because a value-impacting node control depends on them
				List<IrNode> cnd1 = cdg
					.getParentBlocks(current.getParentBlock())
					.stream()
					.map(b -> b.getTerminator())
					.filter(t -> !tcd.contains(t))
					.collect(Collectors.toList());
				
				CDGNode currentCdgNode = cdg.getNode(current.getParentBlock());
				
				// Get all nodes which are on a cycle with the current node
				Multimap<CDGNode, CfgEdge> ccd = cdg.cdgPredecessors(currentCdgNode);
				
				List<IrNode> cnd2 = this.inCycleWith(current.getParentBlock()).stream()
					.map(b -> cdg.getNode(b))
					.filter(c -> {
						if (!lcd.containsKey(c)) // If l is transitively control dependent on c,
							return false;
						
						Collection<CfgEdge> edges = lcd.get(c);
						if (edges.size() != 1) // through exactly one out-edge (say b2),
							return false;
						
						if (!ccd.containsKey(c)) // then a value-impacting node t is not transitively control dependent on c,
							return true;

						CfgEdge dependingEdge = edges.iterator().next();
						CfgEdge candidateEdge = ccd.get(c).iterator().next();  // or if it is, it's not through b2.
						
						if (dependingEdge.equals(candidateEdge))
							return false;
						
						return true; // And c and t are in a cycle.
					})
					.map(c -> c.block.getTerminator())
					.collect(Collectors.toList());
							
				List<IrNode> cnd3 = ccd.asMap().entrySet().stream()
					.filter(c -> {
						CDGNode cdgNode = c.getKey();
						Collection<CfgEdge> edges = c.getValue();
								
						if (edges.size() != 1) // t is transitively control dependent on c through exactly one edge
							return false;
						
						// and l is transitively control dependent on c through on all outgoing edges
						if (!lcd.containsKey(cdgNode))
							return false;
						
						Collection<CfgEdge> criteriaEdges = lcd.get(cdgNode);
						
						return criteriaEdges.size() == cdgNode.block.children().size();						
					})
					.map(c -> c.getKey().block.getTerminator())
					.collect(Collectors.toList());
				
				wl.addAll(cnd1);
				wl.addAll(cnd2);
				wl.addAll(cnd3);
			}
		}
		
		//vi.forEach(dep -> System.out.println(dep.toString()));
		
		// Find required control dependencies
		List<IrNode> controlDeps = new ArrayList<>();
		
		wl.addAll(vi);
		while (!wl.isEmpty()) {
			IrNode current = wl.poll();
			if (!controlDeps.contains(current)) {
				if (!vi.contains(current))
					controlDeps.add(current);
				
				cdg.getParentBlocks(current.getParentBlock()).stream().map(block -> block.getTerminator()).forEach(terminator -> {
					if (!vi.contains(terminator)) {
						wl.add(terminator);
					}
				});
			}			
		}

		//controlDeps.forEach(dep -> System.out.println(dep.toString()));
		
		List<IrNode> visited = new ArrayList<>();
		visited.addAll(controlDeps);
		visited.addAll(vi);
		
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
	
	/**
	 * Returns a list of blocks which are in a cycle with a given block
	 *  
	 * @param block A BasicBlock object
	 * 
	 * @return 
	 */
	private List<BasicBlock> inCycleWith(BasicBlock block) {
		Stack<BasicBlock> wl = new Stack<>();
		List<BasicBlock> visited = new ArrayList<>();
		
		wl.push(block);
		
		// Find all nodes which are reachable from the given block
		while (!wl.isEmpty()) {
			BasicBlock current = wl.pop();
			if (!visited.contains(current)) {
				visited.add(current);
				for (BasicBlock child : current.children()) {
					wl.push(child);
				}
			}
		}
		
		List<BasicBlock> inCycle = new ArrayList<>();
		
		// Find all nodes of the visited list which can reach the given block
		for (BasicBlock visitedBlock : visited) {
			List<BasicBlock> inc = new ArrayList<>();
			wl.push(visitedBlock);
			
			while (!wl.isEmpty()) {
				BasicBlock current = wl.pop();
				if (!inc.contains(current)) {
					inc.add(current);
					for (BasicBlock child : current.children()) {
						wl.push(child);
					}
				}
			}
			
			if (inc.contains(block)) {
				inCycle.add(visitedBlock);
			}
		}
		
		return inCycle;
	}
}
