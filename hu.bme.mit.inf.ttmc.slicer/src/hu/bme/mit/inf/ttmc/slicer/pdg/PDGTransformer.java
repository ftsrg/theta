package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;

public class PDGTransformer {

	private Map<CFGNode, PDGNode> nodes = new HashMap<>();
	private Set<CFGNode> cfgNodes;
	private CFG cfg;
	private Map<CFGNode, Set<CFGNode>> dominators = new HashMap<>();

	public PDGTransformer(CFG cfg)
	{
		this.cfg = cfg;
		this.cfgNodes = this.cfg.nodes();
	}

	public PDG transform()
	{
		Set<CFGNode> nodes = cfg.nodes();

		PDGNode entry = transformNode(cfg.getEntry());

		return new PDG(entry);
	}

	private PDGNode transformNode(CFGNode node) {
		PDGNode pdg = new PDGNode(node);

		this.nodes.put(node, pdg);
		for (CFGNode child : node.getChildren()) {
			if (!this.nodes.containsKey(child)) {
				System.out.println("Node: " + child);
				//Set<CFGNode> dominators = dominators(child, cfg.getInit(), new HashSet<CFGNode>());
				Set<CFGNode> dominated = new HashSet<>(this.cfgNodes);
				Set<CFGNode> reachable = new HashSet<CFGNode>();
				dominators(child, cfg.getEntry(), reachable);

				dominated.removeAll(reachable);
				dominated.remove(child);

				this.dominators.put(child, dominated);
				for (CFGNode dom : dominated) {
					System.out.println("    Dom: " + dom);
				}

				transformNode(child);
			}
		}

		return pdg;
	}

	private Set<CFGNode> dominators(CFGNode node, CFGNode source, Set<CFGNode> visited) {
		visited.add(source);
		for (CFGNode child : source.getChildren()) {
			if (!visited.contains(child) && child != node) {
				dominators(node, child, visited);
			}
		}

		return visited;
	}

	/*
	public PDGNode transformNode(CFGNode cfg)
	{
		PDGNode pdg = new PDGNode(cfg);
		this.nodes.put(cfg, pdg);

		for (CFGNode node : cfg.getChildren()) {
			if (!this.nodes.containsKey(node)) {
				for (CFGNode child : cfg.getChildren()) {
					System.out.println("Node: " + child);
					Set<CFGNode> dominators = findDominators(child, cfg, new HashSet<CFGNode>());

					for (CFGNode dom : dominators) {
						System.out.println("    Dom: " + dom);
					}
				}
				transformNode(node);
			}
		}

		return pdg;
	}

	public Set<CFGNode> findDominators(CFGNode cfg, CFGNode entry, Set<CFGNode> visited)
	{
		visited.add(entry);
		for (CFGNode node : entry.getChildren()) {
			if (!visited.contains(node) && node != cfg) {
				findDominators(cfg, node, visited);
			}
		}

		return visited;
	}
*/
	public static PDG createPDG(CFG cfg)
	{
		PDGTransformer transformer = new PDGTransformer(cfg);
		return transformer.transform();
	}

}
