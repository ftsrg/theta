package hu.bme.mit.inf.ttmc.slicer.graph;

import java.util.Collection;

public interface ReversibleGraphNode extends GraphNode {

	public Collection<? extends ReversibleGraphNode> getParents();

}
