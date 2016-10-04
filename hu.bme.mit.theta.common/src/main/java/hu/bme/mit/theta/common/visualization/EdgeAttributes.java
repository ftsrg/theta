package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkNotNull;

import java.awt.Color;

public final class EdgeAttributes {
	private final String label;
	private final Color color;
	private final LineStyle lineStyle;
	private final String font;

	private EdgeAttributes(final String label, final Color color, final LineStyle lineStyle, final String font) {
		this.label = checkNotNull(label);
		this.color = checkNotNull(color);
		this.lineStyle = checkNotNull(lineStyle);
		this.font = checkNotNull(font);
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

	public static Builder builder() {
		return new Builder();
	}

	public static class Builder {
		private String label = "";
		private Color color = Color.BLACK;
		private LineStyle lineStyle = LineStyle.NORMAL;
		private String font = "";

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

		public Builder font(final String font) {
			this.font = font;
			return this;
		}

		public EdgeAttributes build() {
			return new EdgeAttributes(label, color, lineStyle, font);
		}
	}
}
