package hu.bme.mit.theta.common.visualization;

import java.awt.Color;

public final class EdgeAttributes {
	private final String label;
	private final Color edgeColor;
	private final LineStyle lineStyle;

	public EdgeAttributes(final String label, final Color edgeColor, final LineStyle lineStyle) {
		super();
		this.label = label;
		this.edgeColor = edgeColor;
		this.lineStyle = lineStyle;
	}

	public String getLabel() {
		return label;
	}

	public Color getEdgeColor() {
		return edgeColor;
	}

	public LineStyle getLineStyle() {
		return lineStyle;
	}

	public static Builder builder() {
		return new Builder();
	}

	public static class Builder {
		private String label = "";
		private Color edgeColor = Color.BLACK;
		private LineStyle lineStyle = LineStyle.NORMAL;

		public Builder label(final String label) {
			this.label = label;
			return this;
		}

		public Builder edgeColor(final Color edgeColor) {
			this.edgeColor = edgeColor;
			return this;
		}

		public Builder lineStyle(final LineStyle lineStyle) {
			this.lineStyle = lineStyle;
			return this;
		}

		public EdgeAttributes build() {
			return new EdgeAttributes(label, edgeColor, lineStyle);
		}
	}
}
