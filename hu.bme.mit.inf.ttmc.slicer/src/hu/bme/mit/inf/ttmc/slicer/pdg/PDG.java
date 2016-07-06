package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.core.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.core.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.GtExpr;
import hu.bme.mit.inf.ttmc.core.expr.IffExpr;
import hu.bme.mit.inf.ttmc.core.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.IteExpr;
import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.LtExpr;
import hu.bme.mit.inf.ttmc.core.expr.ModExpr;
import hu.bme.mit.inf.ttmc.core.expr.MulExpr;
import hu.bme.mit.inf.ttmc.core.expr.NegExpr;
import hu.bme.mit.inf.ttmc.core.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.OrExpr;
import hu.bme.mit.inf.ttmc.core.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.RemExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.core.utils.impl.FailExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.Graph;

public class PDG implements Graph {

	private PDGNode entry;

	public PDG(PDGNode entry) {
		this.entry = entry;
	}

	@Override
	public PDGNode getEntry() {
		return entry;
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

				System.out.println(outerStmtNode + " --D--> " + innerStmtNode + "\n" + outerLVars + "\n" + innerRVars);
				// X --D--> Y, if LV(X) intersect RV(Y) is not empty
				boolean changed = innerRVars.retainAll(outerLVars);
				System.out.println(innerRVars);
				System.out.println(changed);

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
		return new PDG(pdgEntry);
	}

}
