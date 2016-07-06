package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.slicer.graph.Graph;

public class CFG implements Graph {

	private CFGNode entry;
	private CFGNode exit;

	public CFG() {}

	public CFG(CFGNode entry, CFGNode exit) {
		this.entry = entry;
		this.exit = exit;
	}

	@Override
	public CFGNode getEntry() {
		return entry;
	}

	public CFGNode getExit() {
		return exit;
	}

	public Set<CFGNode> nodes()
	{
		Set<CFGNode> nodes = new HashSet<>();
		DFS(entry, nodes);

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
