package hu.bme.mit.theta.common.visualization;

import java.awt.Color;

public final class EdgeAttributes {
	private final String label;
	private final Color color;
	private final LineStyle lineStyle;

	private EdgeAttributes(final String label, final Color color, final LineStyle lineStyle) {
		this.label = label;
		this.color = color;
		this.lineStyle = lineStyle;
	}

	public String getLabel() {
		return label;
	}

	public Color getColor() {
		return color;
	}

	public LineStyle getLineStyle() {
		return lineStyle;
	}

	public static Builder builder() {
		return new Builder();
	}

	public static class Builder {
		private String label = "";
		private Color color = Color.BLACK;
		private LineStyle lineStyle = LineStyle.NORMAL;

		public Builder label(final String label) {
			this.label = label;
			return this;
		}

		public Builder color(final Color color) {
			this.color = color;
			return this;
		}

		public Builder lineStyle(final LineStyle lineStyle) {
			this.lineStyle = lineStyle;
			return this;
		}

		public EdgeAttributes build() {
			return new EdgeAttributes(label, color, lineStyle);
		}
	}
}
