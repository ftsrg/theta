package hu.bme.mit.inf.ttmc.frontend.dependency;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;

public class ControlDependencyGraph {

	private CDGNode entry;
	private final Map<BasicBlock, CDGNode> nodes;

	public static class CDGNode {
		public final BasicBlock block;
		public final List<CDGNode> children = new ArrayList<>();
		public final List<CDGNode> parents = new ArrayList<>();

		public CDGNode(BasicBlock block) {
			this.block = block;
		}
	}

	private ControlDependencyGraph(Map<BasicBlock, CDGNode> nodes, CDGNode entry) {
		this.nodes = nodes;
		this.entry = entry;
	}

	public Collection<CDGNode> getNodes() {
		return Collections.unmodifiableCollection(this.nodes.values());
	}

	public Collection<BasicBlock> getParentBlocks(BasicBlock block) {
		return this.nodes.get(block).parents.stream()
			.map(p -> p.block)
			.collect(Collectors.toList());
	}

	public static ControlDependencyGraph buildGraph(Function function) {
		List<BasicBlock> blocks = function.getBlocksDFS();
		DominatorTree pdt = DominatorTree.createPostDominatorTree(function);

		/*
		 * Control dependence algorithm from J. Ferrante et al.
		 *
		 * Given the post-dominator tree, we can determine control dependences by examining certain control
		 * flow graph edges and annotating nodes on corresponding tree paths.
		 * Let S consist of all edges (A, B) in the control flow graph such that B is not an ancestor of
		 * A in the post-dominator tree (i.e., B does not post- dominate A).
		 *
		 * The control dependence determination algorithm proceeds by examining each edge (A, B) in S.
		 * Let L denote the least common ancestor of A and B in the post-dominator tree. By construction, we cannot have L equal B.
		 *
		 * Case 1. L = parent of A.
		 * All nodes in the post-dominator tree on the path from L to B, including B but not L,
		 * should be made control dependent on A.
		 *
		 * Case 2. L = A. All nodes in the post-dominator tree on the path from A to B,
		 * including A and B, should be made control dependent on A.
		 * This case captures loop dependence.)
		 *
		 * It should be clear that, given (A, B), the desired effect will be achieved by traversing backwards from B in the post-dominator
		 * tree until we reach A’s parent (if it exists), marking all nodes visited before A’s parent as control dependent on A.
		 */
		Map<BasicBlock, Set<BasicBlock>> controlDeps = new HashMap<>();
		blocks.forEach(b -> controlDeps.put(b, new HashSet<>()));

		for (BasicBlock block : controlDeps.keySet()) {
			// Get the block's (A's) parent
			BasicBlock blockIdom = pdt.getParent(block);
			Set<BasicBlock> dependants = controlDeps.get(block);

			// Get all block -> child (A -> B) edges
			for (BasicBlock child : block.children()) {
				if (!pdt.dominates(child, block)) { // B must not dominate A
					BasicBlock parent = child;
					while (parent != block && parent != blockIdom) {
						if (parent == null)
							break;

						dependants.add(parent);
						parent = pdt.getParent(parent);
					}
				}
			}
		}

		/* After finding the control dependency relation, we can build the control dependency graph */
		Map<BasicBlock, CDGNode> nodes = new HashMap<>();
		for (BasicBlock block : blocks) {
			nodes.put(block, new CDGNode(block));
		}

		CDGNode entry = nodes.get(function.getEntryBlock());
		controlDeps.forEach((BasicBlock block, Set<BasicBlock> deps) -> {
			CDGNode cdg = nodes.get(block);
			deps.forEach(child -> {
				CDGNode childNode = nodes.get(child);
				cdg.children.add(childNode);
				childNode.parents.add(cdg);
			});
		});

		nodes.values().stream().filter(n -> n.parents.size() == 0 && n != entry).forEach(n -> {
			n.parents.add(entry);
			entry.children.add(n);
		});

		return new ControlDependencyGraph(nodes, entry);
	}

}
