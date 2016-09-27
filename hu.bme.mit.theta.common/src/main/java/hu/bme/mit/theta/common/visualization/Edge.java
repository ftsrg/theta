package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkNotNull;

import java.awt.Color;

public final class Edge {

	private final Node source;
	private final Node target;
	private final String label;
	private final Color edgeColor;
	private final String lineStyle;

	Edge(final Node source, final Node target, final String label, final Color edgeColor, final String lineStyle) {
		this.source = checkNotNull(source);
		this.target = checkNotNull(target);
		this.label = checkNotNull(label);
		this.edgeColor = checkNotNull(edgeColor);
		this.lineStyle = checkNotNull(lineStyle);
	}

	public Node getSource() {
		return source;
	}

	public Node getTarget() {
		return target;
	}

	public String getLabel() {
		return label;
	}

	public Color getEdgeColor() {
		return edgeColor;
	}

	public String getLineStyle() {
		return lineStyle;
	}

}
