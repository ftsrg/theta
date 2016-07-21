package hu.bme.mit.inf.ttmc.slicer.optimizer;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.slicer.cfg.BranchStmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGPrinter;
import hu.bme.mit.inf.ttmc.slicer.cfg.DecoratedCFGNode;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTree;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTreeCreator;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphPrinter;

import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assume;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Bool;

public class LoopUnroller implements CFGOptimizer {

	private int depth;

	public LoopUnroller(int depth) {
		this.depth = depth;
	}

	@Override
	public CFG transform(CFG input) {
		CFG cfg = input;
		DominatorTree dt = DominatorTreeCreator.dominatorTree(cfg);

		List<BranchStmtCFGNode> headers = LoopUtils.findLoopHeaders(cfg, dt);

		for (BranchStmtCFGNode head : headers) {
			CFGNode tail = LoopUtils.getBackEdgeTail(head, dt);
			List<CFGNode> body = LoopUtils.getLoopBody(head, tail);

			for (int i = 0; i < this.depth; i++) {
				this.transformLoop(head, tail, body);
			}
		}

		return cfg;
	}

	private void transformLoop(BranchStmtCFGNode head, CFGNode tail, List<CFGNode> body) {
		Map<CFGNode, CFGNode> map = new HashMap<>();

		for (CFGNode node : body) {
			map.put(node, node.copy());
		}

		map.forEach((CFGNode oldNode, CFGNode newNode) -> {
			for (CFGNode child : oldNode.getChildren()) {
				if (map.containsKey(child)) {
					newNode.addChild(map.get(child));
				}
			}
		});

		// Get the first statement in the loop
		CFGNode first = map.get(head.getChildren().get(0));
		CFGNode last = map.get(tail);
		CFGNode elze = head.getElseNode();

		// Remove the back edge
		last.removeChild(map.get(head));

		// Create the If condition node
		BranchStmtCFGNode assume = new BranchStmtCFGNode(Assume(head.getStmt().getCond()));
		assume.addChild(first);

		List<CFGNode> seqParents = head.getParents()
			.stream().filter(s -> s != tail).collect(Collectors.toList());

		seqParents.forEach(s -> {
			s.addChild(assume);
			s.removeChild(head);
		});
		last.addChild(head);

		assume.addChild(elze);
	}

}
