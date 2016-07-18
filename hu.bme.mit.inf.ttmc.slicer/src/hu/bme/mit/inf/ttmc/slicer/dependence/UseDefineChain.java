package hu.bme.mit.inf.ttmc.slicer.dependence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;

/*
 * A use-define chain is a list for each use of a variable of all definitions that reach that use.
 */

public class UseDefineChain {

	/**
	 * Definition information
	 */
	private class Definition {

		/**
		 * The node which defines this variable
		 */
		public StmtCFGNode node;

		/**
		 * The variable defined
		 */
		public VarDecl<? extends Type> var;

		public Definition(StmtCFGNode node, VarDecl<? extends Type> var) {
			this.node = node;
			this.var = var;
		}

		@Override
		public String toString() {
			return node.toString();
		}
	}

	private class NodeInfo {
		public StmtCFGNode node;

		public Set<Definition> gen = new HashSet<>();
		public Set<Definition> kill = new HashSet<>();
		public Set<Definition> in = new HashSet<>();
		public Set<Definition> out = new HashSet<>();

		public List<VarDecl<? extends Type>> def = new ArrayList<>();
		public List<VarDecl<? extends Type>> use = new ArrayList<>();

		public NodeInfo(StmtCFGNode node) {
			this.node = node;
		}
	}

	private CFG cfg;
	private List<StmtCFGNode> nodes;
	private Map<CFGNode, NodeInfo> nodeInfo = new HashMap<>();
	private List<Definition> definitions = new ArrayList<>();


	public UseDefineChain(CFG cfg) {
		this.cfg = cfg;
		this.nodes = cfg.nodes().stream().filter(s -> s instanceof StmtCFGNode).map(s -> (StmtCFGNode) s).collect(Collectors.toList());
		this.buildChain();
	}

	/**
	 * Return all nodes which have a reaching definition to this node's used variables
	 *
	 * @param node
	 *
	 * @return
	 */
	public List<StmtCFGNode> definitionNodes(StmtCFGNode node) {
		NodeInfo info = this.nodeInfo.get(node);

		return info.in.stream()
			.filter(s -> info.use.contains(s.var))
			.map(s -> s.node)
			.collect(Collectors.toList());
	}

	/**
	 * Return all nodes which have a reaching definition to this node's given variable
	 *
	 * @param node
	 *
	 * @return
	 */
	public List<StmtCFGNode> varDefinitionNodes(StmtCFGNode node, VarDecl<? extends Type> var) {
		NodeInfo info = this.nodeInfo.get(node);

		return info.in.stream()
			.filter(s -> s.var == var)
			.map(s -> s.node)
			.collect(Collectors.toList());
	}

	/**
	 * Return a list of all variables used in this node
	 *
	 * @param node
	 *
	 * @return
	 */
	public List<VarDecl<? extends Type>> usedVariables(StmtCFGNode node) {
		NodeInfo info = this.nodeInfo.get(node);

		return Collections.unmodifiableList(info.use);
	}

	private void buildChain() {
		// Find all definitions
		for (StmtCFGNode node : this.nodes) {
			NodeInfo info = new NodeInfo(node);

			Set<VarDecl<? extends Type>> defs = VariableFinderVisitor.findLeftVars(node.getStmt());
			Set<VarDecl<? extends Type>> uses = VariableFinderVisitor.findRightVars(node.getStmt());

			for (VarDecl<? extends Type> var : defs) {
				Definition def = new Definition(node, var);
				info.def.add(var);
				info.gen.add(def);
				this.definitions.add(def);
			}

			info.use.addAll(uses);

			nodeInfo.put(node, info);
		}

		// Compute kill sets
		//	If statement S defines variable X, kill[S] contains every other definitions of X
		for (NodeInfo info : this.nodeInfo.values()) {
			info.kill.addAll(this.definitions.stream().filter(s -> info.def.contains(s.var)).collect(Collectors.toList()));
			info.kill.removeAll(info.gen);
		}

		// Iterative algorithm for reaching definitions.
		// Source: Compilers: Principles, Techniques and Tools, 1st edition, Algorithm 10.2
		for (NodeInfo info : this.nodeInfo.values()) {
			info.out.addAll(info.gen);
		}

		boolean change = true;
		while (change) {
			change = false;
			for (NodeInfo info : this.nodeInfo.values()) {
				// in[S] = for all p in parent(S) Union {out[p]}
				Set<Definition> newIn = new HashSet<>();
				info.node.getParents().forEach(s -> {
					if (s != this.cfg.getEntry()) {
						newIn.addAll(this.nodeInfo.get(s).out);
					}
				});
				info.in = newIn;

				// out[S] = gen[S] union (in[S] sub kill[S])
				Set<Definition> newOut = new HashSet<>(info.gen);
				newOut.addAll(info.in.stream().filter(s -> !info.kill.contains(s)).collect(Collectors.toList()));

				if (!info.out.equals(newOut)) {
					info.out = newOut;
					change = true;
				}
			}
		}
	}
}
