package hu.bme.mit.inf.ttmc.slicer.pdg;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.Graph;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

public class DominanceTree implements Graph {

	private DominanceTreeNode entry;

	public DominanceTree(DominanceTreeNode entry)
	{
		this.entry = entry;
	}

	@Override
	public GraphNode getEntry() {
		return this.entry;
	}



}
