package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import hu.bme.mit.inf.ttmc.slicer.graph.Graph;

public class CFG implements Graph {

	private CFGNode entry;
	private CFGNode exit;

	public CFG() {}

	public CFG(CFGNode entry, CFGNode exit) {
		this.entry = entry;
		this.exit = exit;
	}

	public CFG copy()
	{
		return this.copy(new HashMap<CFGNode, CFGNode>());
	}

	public CFG copy(Map<CFGNode, CFGNode> map)
	{
		List<CFGNode> nodes = this.nodes();

		for (CFGNode node : nodes) {
			CFGNode newNode = node.copy();
			map.put(node, newNode);
		}

		for (CFGNode node : nodes) {
			CFGNode newNode = map.get(node);
			for (CFGNode child : node.getChildren()) {
				newNode.addChild(map.get(child));
			}
		}

		return new CFG(map.get(this.entry), map.get(this.exit));
	}

	@Override
	public CFGNode getEntry() {
		return entry;
	}

	public CFGNode getExit() {
		return exit;
	}

	public List<CFGNode> nodes()
	{
		List<CFGNode> nodes = new ArrayList<>();
		DFS(entry, nodes);

		return nodes;
	}

	private void DFS(CFGNode cfg, List<CFGNode> visited)
	{
		visited.add(cfg);
		for (CFGNode node : cfg.getChildren()) {
			if (!visited.contains(node)) {
				DFS(node, visited);
			}
		}
	}

}
