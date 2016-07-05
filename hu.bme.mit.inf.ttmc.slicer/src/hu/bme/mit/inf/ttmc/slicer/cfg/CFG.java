package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.slicer.graph.Graph;

public class CFG implements Graph {

	private CFGNode init;
	private CFGNode end;

	public CFG() {}

	public CFG(CFGNode init, CFGNode end) { this.setInit(init); this.setEnd(end); }

	public CFGNode getEntry() {
		return init;
	}

	public void setInit(CFGNode init) {
		this.init = init;
	}

	public CFGNode getEnd() {
		return end;
	}

	public void setEnd(CFGNode end) {
		this.end = end;
	}

	public Set<CFGNode> nodes()
	{
		Set<CFGNode> nodes = new HashSet<>();
		DFS(init, nodes);

		return nodes;
	}

	private void DFS(CFGNode cfg, Set<CFGNode> visited)
	{
		visited.add(cfg);
		for (CFGNode node : cfg.getChildren()) {
			if (!visited.contains(node)) {
				DFS(node, visited);
			}
		}
	}

}
