package hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph;

import java.util.ArrayList;
import java.util.List;

/**
 * Generic graph that can be visualized
 * @author Akos
 */
public class Graph {
	private String id;
	private String label;
	private List<Node> nodes;
	
	/**
	 * Initialize graph
	 * @param id Id
	 * @param label Label
	 */
	public Graph(String id, String label){
		this.id = id;
		this.label = label;
		this.nodes = new ArrayList<>();
	}
	
	/**
	 * Get the Id
	 * @return Id
	 */
	public String getId() {
		return id;
	}
	
	/**
	 * Get the label
	 * @return Label
	 */
	public String getLabel() {
		return label;
	}
	
	/**
	 * Get the list of nodes
	 * @return List of nodes
	 */
	public List<Node> getNodes() {
		return nodes;
	}
	
	/**
	 * Add a node
	 * @param node Node to be added
	 */
	public void addNode(Node node){
		nodes.add(node);
	}
	
}
