package hu.bme.mit.inf.ttmc.slicer.graph;

import java.util.Collection;

public interface GraphNode {

	public Collection<? extends GraphNode> getChildren();

	public String getLabel();

}
