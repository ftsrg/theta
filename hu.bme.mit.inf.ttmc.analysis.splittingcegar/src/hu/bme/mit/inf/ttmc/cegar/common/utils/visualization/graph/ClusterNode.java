package hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph;

import java.util.ArrayList;
import java.util.List;

/**
 * A node with subnodes
 * @author Akos
 */
public class ClusterNode extends Node {
	private List<Node> subNodes;
	
	/**
	 * Initialize node
	 * @param id Id
	 * @param label Label
	 * @param color Color
	 * @param isInitial Is the node initial
	 */
	public ClusterNode(String id, String label, String color, String fillColor, String lineStyle, boolean isInitial) {
		super(id, label, color, fillColor, lineStyle, isInitial);
		subNodes = new ArrayList<Node>();
	}

	/**
	 * Get the list of subnodes
	 * @return List of subnodes
	 */
	public List<Node> getSubNodes() {
		return subNodes;
	}
	
	/**
	 * Add a subnode
	 * @param node Subnode
	 */
	public void addSubNode(Node node){
		subNodes.add(node);
	}

}
