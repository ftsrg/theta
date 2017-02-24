package hu.bme.mit.theta.frontend.c.dependency;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.NonTerminatorIrNode;

public class ProgramDependenceGraph {

	public static class PDGNode {
		private final IrNode node;

		private PDGNode(final IrNode node) {
			this.node = node;
		}

		public IrNode getNode() {
			return this.node;
		}
	}

	public static class PDGEdge {
		private final PDGNode source;
		private final PDGNode target;

		PDGEdgeType type;

		private PDGEdge(final PDGNode source, final PDGNode target, final PDGEdgeType type) {
			this.source = source;
			this.target = target;
			this.type = type;
		}

		public PDGNode getSource() {
			return this.source;
		}

		public PDGNode getTarget() {
			return this.target;
		}

		public PDGEdgeType getType() {
			return this.type;
		}
	}

	public enum PDGEdgeType {
		CONTROL, DATA
	}

	private final Map<IrNode, PDGNode> nodes;
	private final Collection<PDGEdge> edges;

	public ProgramDependenceGraph(final Map<IrNode, PDGNode> nodes, final Collection<PDGEdge> edges) {
		this.nodes = nodes;
		this.edges = edges;
	}

	public Collection<PDGNode> getNodes() {
		return this.nodes.values();
	}

	public Collection<PDGEdge> getEdges() {
		return this.edges;
	}

	public static ProgramDependenceGraph create(final Function function) {
		final ControlDependencyGraph cdg = ControlDependencyGraph.buildGraph(function);
		final UseDefineChain ud = UseDefineChain.buildChain(function);

		final Map<IrNode, PDGNode> nodes = new HashMap<>();
		final List<PDGEdge> edges = new ArrayList<>();

		// Construct the graph initially
		for (final BasicBlock block : function.getBlocks()) {
			for (final IrNode node : block.getAllNodes()) {
				nodes.put(node, new PDGNode(node));
			}
		}

		for (final Entry<IrNode, PDGNode> entry : nodes.entrySet()) {
			final IrNode node = entry.getKey();
			final PDGNode pdg = entry.getValue();

			// Get all control dependencies of this edge
			final List<BasicBlock> controlDeps = cdg.getParentBlocks(node.getParentBlock());
			final List<NonTerminatorIrNode> flowDeps = ud.getDefinitions(node);

			for (final BasicBlock block : controlDeps) {
				final PDGNode terminator = nodes.get(block.getTerminator());
				edges.add(new PDGEdge(terminator, pdg, PDGEdgeType.CONTROL));
			}

			for (final IrNode flowDep : flowDeps) {
				final PDGNode def = nodes.get(flowDep);
				edges.add(new PDGEdge(def, pdg, PDGEdgeType.DATA));
			}

		}

		return new ProgramDependenceGraph(nodes, edges);
	}

}
