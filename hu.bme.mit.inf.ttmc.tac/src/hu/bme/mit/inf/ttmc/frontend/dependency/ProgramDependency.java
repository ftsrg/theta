package hu.bme.mit.inf.ttmc.frontend.dependency;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;

public final class ProgramDependency {

	public static class PDGNode {
		private final IrNode node;
		private final List<PDGNode> controlChildren = new ArrayList<>();
		private final List<PDGNode> controlParents = new ArrayList<>();

		private final List<PDGNode> flowParents = new ArrayList<>();
		private final List<PDGNode> flowChildren = new ArrayList<>();

		public PDGNode(IrNode node) {
			this.node = node;
		}

		public Collection<PDGNode> parents() {
			Set<PDGNode> parents = new HashSet<>();
			parents.addAll(this.controlParents);
			parents.addAll(this.flowParents);

			return parents;
		}

		public IrNode getNode() {
			return node;
		}

		public List<PDGNode> getControlChildren() {
			return controlChildren;
		}

		public List<PDGNode> getControlParents() {
			return controlParents;
		}

		public List<PDGNode> getFlowParents() {
			return flowParents;
		}

		public List<PDGNode> getFlowChildren() {
			return flowChildren;
		}

		@Override
		public String toString() {
			return node.getLabel();
		}
	}

	private final Function function;
	private final Map<IrNode, PDGNode> nodes;
	private final PDGNode entry;

	private ProgramDependency(Map<IrNode, PDGNode> nodes, PDGNode entry, Function function) {
		this.nodes = nodes;
		this.entry = entry;
		this.function = function;
	}

	public PDGNode findNode(IrNode node) {
		return this.nodes.get(node);
	}

	public static ProgramDependency buildPDG(Function function) {
		DominatorTree pdt = DominatorTree.createPostDominatorTree(function);
		UseDefineChain ud = UseDefineChain.buildChain(function);

		List<BasicBlock> blocks = function.getBlocksDFS();

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
		Map<IrNode, PDGNode> nodes = new HashMap<>();
		for (BasicBlock block : blocks) {
			for (IrNode node : block.getAllNodes()) {
				nodes.put(node, new PDGNode(node));
			}
		}

		PDGNode entry = nodes.get(function.getEntryBlock().getTerminator());

		controlDeps.forEach((BasicBlock block, Set<BasicBlock> deps) -> {
			// If B is control dependant on A, all of A's nodes are control dependant on B's terminator
			PDGNode terminator = nodes.get(block.getTerminator());
			deps.forEach(dep -> {
				List<PDGNode> pdgNodes = dep.getAllNodes().stream().map(n -> nodes.get(n)).collect(Collectors.toList());
				pdgNodes.forEach(p -> {
					terminator.controlChildren.add(p);
					p.controlParents.add(terminator);
				});
			});
		});

		// If node does not depend on any node, it should depend on the entry node
		nodes.values().stream().filter(p -> p.controlParents.size() == 0 && p != entry).forEach(p -> {
			p.controlParents.add(entry);
			entry.controlChildren.add(p);
		});

		/*
		 * Perform flow dependency calculation
		 */
		for (PDGNode pdg : nodes.values()) {
			ud.getDefinitions(pdg.node).stream()
				.map(d -> nodes.get(d))
				.filter(p -> p != pdg)
				.forEach(p -> {
					pdg.flowParents.add(p);
					p.flowChildren.add(pdg);
				});
		}


		return new ProgramDependency(nodes, entry, function);
	}

	public Collection<PDGNode> getNodes() {
		return nodes.values();
	}

	public PDGNode getEntry() {
		return this.entry;
	}

}
