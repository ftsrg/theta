package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkNotNull;

import java.awt.Color;

public final class NodeAttributes {
	private final String label;
	private final Color lineColor;
	private final Color fillColor;
	private final LineStyle lineStyle;
	private final int peripheries;
	private final Shape shape;

	private NodeAttributes(final String label, final Color lineColor, final Color fillColor, final LineStyle lineStyle,
			final int peripheries, final Shape shape) {
		this.label = checkNotNull(label);
		this.lineColor = checkNotNull(lineColor);
		this.fillColor = checkNotNull(fillColor);
		this.lineStyle = checkNotNull(lineStyle);
		this.peripheries = peripheries;
		this.shape = checkNotNull(shape);
	}

	public String getLabel() {
		return label;
	}

	public Color getLineColor() {
		return lineColor;
	}

	public Color getFillColor() {
		return fillColor;
	}

	public LineStyle getLineStyle() {
		return lineStyle;
	}

	public int getPeripheries() {
		return peripheries;
	}

	public Shape getShape() {
		return shape;
	}

	public static Builder builder() {
		return new Builder();
	}

	public static class Builder {
		private String label = "";
		private Color lineColor = Color.BLACK;
		private Color fillColor = Color.WHITE;
		private LineStyle lineStyle = LineStyle.NORMAL;
		private int peripheries = 1;
		private Shape shape = Shape.ELLIPSE;

		public Builder label(final String label) {
			this.label = label;
			return this;
		}

		public Builder lineColor(final Color lineColor) {
			this.lineColor = lineColor;
			return this;
		}

		public Builder fillColor(final Color fillColor) {
			this.fillColor = fillColor;
			return this;
		}

		public Builder lineStyle(final LineStyle lineStyle) {
			this.lineStyle = lineStyle;
			return this;
		}

		public Builder peripheries(final int peripheries) {
			this.peripheries = peripheries;
			return this;
		}

		public Builder shape(final Shape shape) {
			this.shape = shape;
			return this;
		}

		public NodeAttributes build() {
			return new NodeAttributes(label, lineColor, fillColor, lineStyle, peripheries, shape);
		}
	}
}
