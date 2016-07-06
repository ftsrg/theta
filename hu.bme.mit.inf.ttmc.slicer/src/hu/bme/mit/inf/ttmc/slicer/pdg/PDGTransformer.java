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
/*
	public PDG transform()
	{
		DominanceTree fdt = DominanceTree.fromCFG(this.cfg);

	}

	public static PDG createPDG(CFG cfg)
	{
		PDGTransformer transformer = new PDGTransformer(cfg);
		return transformer.transform();
	}
*/
}
