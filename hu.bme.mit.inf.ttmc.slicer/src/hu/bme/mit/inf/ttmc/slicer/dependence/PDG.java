package hu.bme.mit.inf.ttmc.slicer.dependence;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTree;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTreeCreator;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTreeNode;
import hu.bme.mit.inf.ttmc.slicer.graph.Graph;

public class PDG implements Graph {

	private PDGNode entry;
	private Map<CFGNode, PDGNode> cfgMap = new HashMap<>();

	public PDG(PDGNode entry) {
		this.entry = entry;
	}

	@Override
	public PDGNode getEntry() {
		return entry;
	}

	public PDGNode findCFGNode(CFGNode cfg)
	{
		return this.cfgMap.get(cfg);
	}

	public static PDG fromCFG(CFG cfg) {
		Set<CFGNode> nodes = cfg.nodes();

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
		Map<CFGNode, Set<CFGNode>> controlDeps = new HashMap<>();
		DominatorTree pdt = DominatorTreeCreator.postDominatorTree(cfg);

		for (CFGNode node : nodes) {
			Set<CFGNode> dependants = new HashSet<CFGNode>();
			controlDeps.put(node, dependants);
			DominatorTreeNode A = pdt.find(node);

			// Get all A -> B edges
			for (CFGNode child : node.getChildren()) {
				DominatorTreeNode B = pdt.find(child);

				if (!pdt.dominates(B, A)) { // B must not postdominate A
					DominatorTreeNode parent = B;
					while (parent != A && parent != A.getParent()) {
						if (parent == null)
							break;
						dependants.add(parent.getCFGNode()); // Add all encountered nodes to the dependants
						parent = parent.getParent();
					}
				}
			}
		}

		/* Start building the tree, first create a map containing the CFG nodes */
		Map<CFGNode, PDGNode> cdgMap = new HashMap<CFGNode, PDGNode>();
		for (CFGNode node : nodes) {
			PDGNode pdgNode = new PDGNode(node);
			cdgMap.put(node, pdgNode);
		}

		/* Add all control children to their parents */
		for (CFGNode node : nodes) {
			PDGNode pdgNode = cdgMap.get(node);
			for (CFGNode dependant : controlDeps.get(node)) {
				pdgNode.addControlChild(cdgMap.get(dependant));
			}
		}

		/* If a node does not control depend on any other (regular) node, it should be dependant on the root node. */
		PDGNode pdgEntry = cdgMap.get(cfg.getEntry());
		for (PDGNode pdgNode : cdgMap.values()) {
			if (pdgNode == pdgEntry)
				continue;

			if (pdgNode.getControlParents().isEmpty()) {
				pdgNode.addControlParent(pdgEntry);
			}
		}

		/*
		 * Build data dependence
		 *
		 * Data/flow dependence occurs when statement Q uses a variable set/written by statement P.
		 * To find whether Q flow depends on P we must find two set of variables:
		 * 	LV(S) := The set of variables S writes
		 *  RV(S) := The set of variables S reads
		 *
		 * Q is data dependant on P if:
		 * 	1. Q is a successor of P in the CFG
		 * 	2. LV(P) intersect RV(Q) is not empty.
		 */
		for (CFGNode outer : cdgMap.keySet()) {
			Set<CFGNode> succ = outer.getSuccessors();
			for (CFGNode inner : succ) {
				if (outer == inner)
					continue;

				if (!(outer instanceof StmtCFGNode) || !(inner instanceof StmtCFGNode))
					continue;

				StmtCFGNode outerStmtNode = (StmtCFGNode) outer;
				StmtCFGNode innerStmtNode = (StmtCFGNode) inner;

				Set<VarDecl<? extends Type>> outerLVars = VariableFinderVisitor.findLeftVars(outerStmtNode.getStmt());
				Set<VarDecl<? extends Type>> innerRVars = VariableFinderVisitor.findRightVars(innerStmtNode.getStmt());

				innerRVars.retainAll(outerLVars);

				if (!innerRVars.isEmpty()) {
					cdgMap.get(outer).addFlowChild(cdgMap.get(inner));
				}
			}
		}

		PDG pdg = new PDG(pdgEntry);
		pdg.cfgMap.putAll(cdgMap);

		return pdg;
	}

}
