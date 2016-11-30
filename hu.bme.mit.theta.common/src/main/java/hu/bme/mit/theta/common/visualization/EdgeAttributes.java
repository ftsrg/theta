package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkNotNull;

import java.awt.Color;

public final class EdgeAttributes {
	private final String label;
	private final Color color;
	private final LineStyle lineStyle;
	private final String font;
	private final int weight;

	private EdgeAttributes(final String label, final Color color, final LineStyle lineStyle, final String font,
			final int weight) {
		this.label = label;
		this.color = color;
		this.lineStyle = lineStyle;
		this.font = font;
		this.weight = weight;
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

	public String getFont() {
		return font;
	}

	public int getWeight() {
		return weight;
	}

	public static Builder builder() {
		return new Builder();
	}

	public static class Builder {
		private String label = "";
		private Color color = Color.BLACK;
		private LineStyle lineStyle = LineStyle.NORMAL;
		private String font = "";
		private int weight = 1;

		public Builder label(final String label) {
			this.label = checkNotNull(label);
			return this;
		}

		public Builder color(final Color color) {
			this.color = checkNotNull(color);
			return this;
		}

		public Builder lineStyle(final LineStyle lineStyle) {
			this.lineStyle = checkNotNull(lineStyle);
			return this;
		}

		public Builder font(final String font) {
			this.font = checkNotNull(font);
			return this;
		}

		public Builder weight(final int weight) {
			this.weight = weight;
			return this;
		}

		public EdgeAttributes build() {
			return new EdgeAttributes(label, color, lineStyle, font, weight);
		}
	}
}
