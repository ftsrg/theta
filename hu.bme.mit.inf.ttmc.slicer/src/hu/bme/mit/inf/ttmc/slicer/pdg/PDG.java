package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;
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
		PostDominanceTree pdt = PostDominanceTree.fromCFG(cfg);
		Set<CFGNode> nodes = cfg.nodes();

		Map<CFGNode, Set<CFGNode>> controlDeps = new HashMap<>();

		for (CFGNode node : nodes) {
			Set<CFGNode> dependants = new HashSet<CFGNode>();
			controlDeps.put(node, dependants);
			DominanceTreeNode A = pdt.findCFGNode(node);

			// Get all A -> B edges
			for (CFGNode child : node.getChildren()) {
				DominanceTreeNode B = pdt.findCFGNode(child);

				if (!pdt.dominates(B, A)) { // B must not postdominate A
					DominanceTreeNode parent = B;
					while (parent != A && parent != A.getParent()) {
						if (parent == null)
							break;
						dependants.add(parent.getCFGNode());
						parent = parent.getParent();
					}
				}
			}
		}

		Map<CFGNode, PDGNode> cdgMap = new HashMap<CFGNode, PDGNode>();
		for (CFGNode node : nodes) {
			PDGNode pdgNode = new PDGNode(node);
			cdgMap.put(node, pdgNode);
		}

		for (CFGNode node : nodes) {
			PDGNode pdgNode = cdgMap.get(node);
			for (CFGNode dependant : controlDeps.get(node)) {
				pdgNode.addControlChild(cdgMap.get(dependant));
			}
		}

		PDGNode pdgEntry = cdgMap.get(cfg.getEntry());
		for (PDGNode pdgNode : cdgMap.values()) {
			if (pdgNode == pdgEntry)
				continue;

			if (pdgNode.getControlParents().isEmpty()) {
				pdgNode.addControlParent(pdgEntry);
			}
		}

		// Build data dependence
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

				//System.out.println(outerStmtNode + " --D--> " + innerStmtNode + "\n" + outerLVars + "\n" + innerRVars);
				// X --D--> Y, if LV(X) intersect RV(Y) is not empty
				boolean changed = innerRVars.retainAll(outerLVars);
				//System.out.println(innerRVars);
				//System.out.println(changed);

				if (!innerRVars.isEmpty()) {
					cdgMap.get(outer).addFlowChild(cdgMap.get(inner));
				}
			}
		}

		/*
		for (PDGNode outer : cdgMap.values()) {
			for (PDGNode inner : cdgMap.values()) {
				if (outer == inner || !(outer.getCfg() instanceof StmtCFGNode)
						|| !(inner.getCfg() instanceof StmtCFGNode))
					continue;

				StmtCFGNode outerStmtNode = (StmtCFGNode) outer.getCfg();
				StmtCFGNode innerStmtNode = (StmtCFGNode) inner.getCfg();

				Set<VarDecl<? extends Type>> outerLVars = VariableFinderVisitor.findLeftVars(outerStmtNode.getStmt());
				Set<VarDecl<? extends Type>> innerRVars = VariableFinderVisitor.findRightVars(innerStmtNode.getStmt());

				System.out.println(outerStmtNode + " --D--> " + innerStmtNode + "\n" + outerLVars + "\n" + innerRVars);
				// X --D--> Y, if LV(X) intersect RV(Y) is not empty
				boolean changed = innerRVars.retainAll(outerLVars);
				System.out.println(innerRVars);
				System.out.println(changed);

				if (!innerRVars.isEmpty()) {
					outer.addFlowChild(inner);
				}
			}

			for (Entry<CFGNode, Set<CFGNode>> e : controlDeps.entrySet()) {
				//System.out.println(e.getKey() + " " + e.getValue());
			}
		}
		*/
/*
		for (PDGNode pdgNode : cdgMap.values()) {
			if (pdgNode == pdgEntry)
				continue;

			pdgNode.addFlowParent(pdgEntry);
		}
*/
		PDG pdg = new PDG(pdgEntry);
		pdg.cfgMap.putAll(cdgMap);

		return pdg;
	}

}
