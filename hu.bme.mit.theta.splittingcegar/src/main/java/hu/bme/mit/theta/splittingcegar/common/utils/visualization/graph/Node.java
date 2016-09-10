package hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Node {
	private final String id;
	private final String label;
	private final String color;
	private final String fillColor;
	private final String lineStyle;
	private final boolean isInitial;
	private final List<String> successors;
	private final Map<String, String> arcColors;

	public Node(final String id, final String label, final String color, final String fillColor, final String lineStyle, final boolean isInitial) {
		this.id = checkNotNull(id);
		this.label = checkNotNull(label);
		this.color = checkNotNull(color);
		this.fillColor = checkNotNull(fillColor);
		this.lineStyle = checkNotNull(lineStyle);
		this.isInitial = isInitial;
		this.successors = new ArrayList<>();
		this.arcColors = new HashMap<>();
	}

	public String getId() {
		return id;
	}

	public String getLabel() {
		return label;
	}

	public String getColor() {
		return color;
	}

	public String getFillColor() {
		return fillColor;
	}

	public String getLineStyle() {
		return lineStyle;
	}

	public boolean isInitial() {
		return isInitial;
	}

	public List<String> getSuccessors() {
		return successors;
	}

	public void addSuccessor(final String id, final String color) {
		successors.add(id);
		if (!"".equals(color))
			arcColors.put(id, color);
	}

	public String getArcColor(final String id) {
		if (arcColors.containsKey(id))
			return arcColors.get(id);
		else
			return "";
	}

}
