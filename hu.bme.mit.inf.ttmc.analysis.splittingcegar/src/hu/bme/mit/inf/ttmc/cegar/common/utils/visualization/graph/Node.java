package hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Generic node that can be visualized
 * @author Akos
 */
public class Node {
	private String id;
	private String label;
	private String color;
	private String fillColor;
	private String lineStyle;
	private boolean isInitial;
	private List<String> successors;
	private Map<String, String> arcColors;
	
	/**
	 * Initialize node
	 * @param id Id
	 * @param label Label
	 * @param color Color
	 * @param isInitial Is the node initial
	 */
	public Node(String id, String label, String color, String fillColor, String lineStyle, boolean isInitial){
		this.id = id;
		this.label = label;
		this.color = color;
		this.fillColor = fillColor;
		this.lineStyle = lineStyle;
		this.isInitial = isInitial;
		this.successors = new ArrayList<>();
		this.arcColors = new HashMap<>();
	}
	
	/**
	 * Get the id
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
	 * Get the color
	 * @return Color
	 */
	public String getColor() {
		return color;
	}
	
	public String getFillColor(){
		return fillColor;
	}
	
	public String getLineStyle(){
		return lineStyle;
	}
	
	/**
	 * Get whether the node is initial
	 * @return True if the node is initial, false otherwise
	 */
	public boolean isInitial() {
		return isInitial;
	}
	
	/**
	 * Get the list of successors
	 * @return List of successors
	 */
	public List<String> getSuccessors() {
		return successors;
	}
	
	/**
	 * Add a successor
	 * @param id Id of the successor
	 */
	public void addSuccessor(String id, String color){
		successors.add(id);
		if (!"".equals(color)) arcColors.put(id, color);
	}
	
	/**
	 * Get the color of an arc
	 * @param id Id of the successor
	 * @return Color of the arc
	 */
	public String getArcColor(String id){
		if (arcColors.containsKey(id))
			return arcColors.get(id);
		else return "";
	}
	
}
