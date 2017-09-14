/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *  
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *  
 *      http://www.apache.org/licenses/LICENSE-2.0
 *  
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.common.visualization.writer;

import java.awt.Color;
import java.io.File;
import java.io.IOException;

import hu.bme.mit.theta.common.visualization.CompositeNode;
import hu.bme.mit.theta.common.visualization.Edge;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.Node;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.common.visualization.Shape;

/**
 * Class for writing graphs in GraphViz format.
 *
 * Known limitations (due to GraphViz):
 *
 * - Fill color of composite nodes is ignored.
 *
 * - Shape of composite nodes is ignored.
 *
 * - Peripheries of composite nodes are ignored.
 */
public final class GraphvizWriter extends AbstractGraphWriter {

	public static enum Format {
		PDF("Tpdf"), PNG("Tpng"), SVG("Tsvg"), GIF("Tgif"), EPS("Teps"), JPG("Tjpg");

		private final String option;

		private Format(final String option) {
			this.option = option;
		}

		private String getOption() {
			return option;
		}
	}

	private GraphvizWriter() {
	}

	private static class LazyHolder {
		static final GraphvizWriter INSTANCE = new GraphvizWriter();
	}

	public static GraphvizWriter getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public String writeString(final Graph graph) {
		final StringBuilder sb = new StringBuilder();
		sb.append("digraph ").append(graph.getId()).append(" {").append(System.lineSeparator());
		sb.append("\tlabel=\"").append(graph.getLabel()).append("\";").append(System.lineSeparator());

		graph.getRootNodes().forEach(n -> printNode(n, sb));

		for (final Node node : graph.getNodes()) {
			printEdges(node, sb);
		}
		sb.append("}");
		return sb.toString();
	}

	public void writeFile(final Graph graph, final String fileName, final Format format)
			throws IOException, InterruptedException {
		final String dotFile = fileName + ".dot";
		super.writeFile(graph, dotFile);
		final Process proc = Runtime.getRuntime()
				.exec("dot.exe -" + format.getOption() + " \"" + dotFile + "\" -o \"" + fileName + "\"");
		proc.waitFor();
		final boolean deleteSuccessful = new File(dotFile).delete();
		if (!deleteSuccessful) {
			throw new IOException("Could not delete temporary dot file.");
		}
	}

	private void printNode(final Node node, final StringBuilder sb) {
		if (node instanceof CompositeNode) {
			printCompositeNode((CompositeNode) node, sb);
		} else {
			printSimpleNode(node, sb);
		}

	}

	private void printSimpleNode(final Node node, final StringBuilder sb) {
		final NodeAttributes attributes = node.getAttributes();

		String style = mapLineStyleToString(attributes.getLineStyle());
		if (!style.equals("")) {
			style += ",";
		}
		style += "filled";

		sb.append("\t\t").append(node.getId());
		sb.append(" [label=\"").append(attributes.getLabel().replace("\n", "\\n")).append("\"");
		if (attributes.getPeripheries() > 1) {
			sb.append(",peripheries=").append(attributes.getPeripheries());
		}
		sb.append(",style=\"").append(style).append("\"");
		sb.append(",fillcolor=").append(mapColorToString(attributes.getFillColor()));
		sb.append(",color=").append(mapColorToString(attributes.getLineColor()));
		sb.append(",shape=").append(mapShapeToString(attributes.getShape()));
		sb.append("];").append(System.lineSeparator());
	}

	private void printCompositeNode(final CompositeNode node, final StringBuilder sb) {
		final NodeAttributes attributes = node.getAttributes();
		final String style = mapLineStyleToString(attributes.getLineStyle());

		sb.append("\tsubgraph cluster_").append(node.getId()).append(" {").append(System.lineSeparator());
		sb.append("\t\tcolor=").append(mapColorToString(attributes.getLineColor())).append(";")
				.append(System.lineSeparator());
		if (!style.equals("")) {
			sb.append("\t\tstyle=").append(style).append(";").append(System.lineSeparator());
		}
		sb.append("\t\tlabel=\"").append(attributes.getLabel().replace("\n", "\\n")).append("\";")
				.append(System.lineSeparator());
		for (final Node child : node.getChildren()) {
			printNode(child, sb);
		}
		sb.append("\t}").append(System.lineSeparator());
	}

	private void printEdges(final Node node, final StringBuilder sb) {
		if (node instanceof CompositeNode) {
			if (node.getOutEdges().size() != 0) {
				throw new UnsupportedOperationException("GraphViz does not support edges between clusters.");
			}
		} else {
			for (final Edge edge : node.getOutEdges()) {
				final EdgeAttributes attributes = edge.getAttributes();
				sb.append("\t").append(edge.getSource().getId()).append(" -> ").append(edge.getTarget().getId());
				sb.append(" [label=\"").append(attributes.getLabel().replace("\n", "\\n")).append("\"");
				sb.append(",color=").append(mapColorToString(attributes.getColor()));
				final String style = mapLineStyleToString(attributes.getLineStyle());
				if (!style.equals("")) {
					sb.append(",style=").append(style);
				}
				if (!attributes.getFont().equals("")) {
					sb.append(",fontname=\"").append(attributes.getFont()).append("\"");
				}
				if (attributes.getWeight() != 1) {
					sb.append(",weight=\"").append(attributes.getWeight()).append("\"");
				}
				sb.append("];").append(System.lineSeparator());
			}
		}
	}

	private String mapColorToString(final Color color) {
		return String.format("\"#%02X%02X%02X\"", color.getRed(), color.getGreen(), color.getBlue());
	}

	private String mapLineStyleToString(final LineStyle lineStyle) {
		switch (lineStyle) {
		case DASHED:
			return "dashed";
		case DOTTED:
			return "dotted";
		case NORMAL:
			return "solid";
		default:
			throw new UnsupportedOperationException("Unknown line style: " + lineStyle + ".");
		}
	}

	private String mapShapeToString(final Shape shape) {
		switch (shape) {
		case CIRCLE:
			return "circle";
		case ELLIPSE:
			return "ellipse";
		case RECTANGLE:
			return "rectangle";
		default:
			throw new UnsupportedOperationException("Unknown shape: " + shape + ".");
		}
	}
}
