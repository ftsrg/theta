package hu.bme.mit.inf.ttmc.slicer.cfa;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.formalism.cfa.impl.ImmutableCFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.impl.MutableCFA;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.slicer.cfg.BranchStmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;

import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assume;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;

public class CFGToCFATransformer {

	public static CFA transform(CFG cfg)
	{
		MutableCFA cfa = new MutableCFA();
		List<StmtCFGNode> nodes = cfg.nodes().stream()
			.filter(s -> s instanceof StmtCFGNode)
			.map(s -> (StmtCFGNode) s)
			.collect(Collectors.toList());

		Map<CFGNode, CFALoc> mapping = new HashMap<>();
		mapping.put(cfg.getExit(), cfa.getFinalLoc());

		for (CFGNode node : nodes) {
			CFALoc loc = cfa.createLoc();
			mapping.put(node, loc);
		}

		// XXX
		// Remove/replace the orphaned init node
		cfa.removeLoc(mapping.get(cfg.getEntry().getChildren().get(0)));
		mapping.put(cfg.getEntry().getChildren().get(0), cfa.getInitLoc());

		for (StmtCFGNode node : nodes) {
			CFALoc source = mapping.get(node);
			boolean isAssert = (node.getStmt() instanceof AssertStmt);
			if (node instanceof BranchStmtCFGNode) {
				BranchStmtCFGNode branch = (BranchStmtCFGNode) node;
				CFGNode then = branch.getThenNode();
				CFGNode elze = branch.getElseNode();

				CFALoc thenTarget = mapping.get(then);
				CFALoc elzeTarget = mapping.get(elze);

				CFAEdge thenEdge = cfa.createEdge(source, thenTarget);
				CFAEdge elzeEdge = cfa.createEdge(source, elzeTarget);

				thenEdge.getStmts().add(branch.getStmt());
				elzeEdge.getStmts().add(Assume(Not(branch.getStmt().getCond())));
			} else {
				for (CFGNode child : node.getChildren()) {
					CFALoc target = mapping.get(child);
					CFAEdge edge = cfa.createEdge(source, target);

					if (isAssert) {
						AssertStmt assertStmt = (AssertStmt) node.getStmt();
						edge.getStmts().add(Assume(assertStmt.getCond()));

						CFAEdge fail = cfa.createEdge(source, cfa.getErrorLoc());
						fail.getStmts().add(Assume(Not(assertStmt.getCond())));
					} else {
						edge.getStmts().add(node.getStmt());
					}
				}
			}
		}

		return ImmutableCFA.copyOf(cfa);
	}

}
