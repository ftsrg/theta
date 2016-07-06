package hu.bme.mit.inf.ttmc.slicer.cfg;

import hu.bme.mit.inf.ttmc.slicer.graph.GraphEdge;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphNode;

public class CFGEdge implements GraphEdge {

	private CFGNode head;
	private CFGNode tail;

	@Override
	public GraphNode getHead() {
		return this.head;
	}

	@Override
	public GraphNode getTail() {
		return this.tail;
	}



}
