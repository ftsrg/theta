package hu.bme.mit.inf.ttmc.slicer.dependence;

import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.slicer.cfg.BranchStmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTree;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTreeCreator;
import hu.bme.mit.inf.ttmc.slicer.optimizer.LoopUtils;

public class LoopAnalysis {

	private CFG cfg;
	private DominatorTree dt;
	private List<BranchStmtCFGNode> loopHeads;

	public LoopAnalysis(CFG cfg) {
		this.cfg = cfg;
		this.dt = DominatorTreeCreator.dominatorTree(this.cfg);
		this.loopHeads = this.findLoopHeaders();
	}

	public List<StmtCFGNode> findLoopInvariants(BranchStmtCFGNode branch) {
		/*
		 * Statement S in loop L is invariant in L, if:
		 * 	All of RV(S) have reaching definitions only outside of the loop.
		 */
		List<CFGNode> loop = LoopUtils.getLoopBody(branch, LoopUtils.getBackEdgeTail(branch, this.dt));

		return null;
	}

	public List<BranchStmtCFGNode> findLoopHeaders() {
		List<BranchStmtCFGNode> loops = this.cfg.nodes().stream()
			.filter(s -> s instanceof BranchStmtCFGNode)
			.map(s -> (BranchStmtCFGNode) s)
			.filter(s -> LoopUtils.isLoopHeader(s, this.dt))
			.collect(Collectors.toList());

		return loops;
	}

}
