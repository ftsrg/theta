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

import hu.bme.mit.theta.common.visualization.CompositeNode;
import hu.bme.mit.theta.common.visualization.Edge;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.Node;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.common.visualization.Shape;

/**
 * Class for writing graphs in yED (GraphML) format.
 */
public final class YedWriter extends AbstractGraphWriter {

	private YedWriter() {
	}

	private static class LazyHolder {
		static final YedWriter INSTANCE = new YedWriter();
	}

	public static YedWriter getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public String writeString(final Graph graph) {
		final StringBuilder sb = new StringBuilder();
		sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>").append(System.lineSeparator());
		sb.append("<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\"").append(System.lineSeparator());
		sb.append("\txmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"").append(System.lineSeparator());
		sb.append("\txmlns:y=\"http://www.yworks.com/xml/graphml\"").append(System.lineSeparator());
		sb.append("\txmlns:yed=\"http://www.yworks.com/xml/yed/3\"").append(System.lineSeparator());
		sb.append(
				"\txsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns http://www.yworks.com/xml/schema/graphml/1.1/ygraphml.xsd\">")
				.append(System.lineSeparator());
		sb.append("<key for=\"node\" id=\"d6\" yfiles.type=\"nodegraphics\"/>").append(System.lineSeparator());
		sb.append("<key for=\"edge\" id=\"d9\" yfiles.type=\"edgegraphics\"/>").append(System.lineSeparator());
		sb.append("<graph edgedefault=\"directed\" id=\"" + graph.getId() + "\">").append(System.lineSeparator());

		graph.getRootNodes().forEach(n -> printNode(n, sb));

		for (final Node node : graph.getNodes()) {
			printEdges(node, sb);
		}

		sb.append("</graph>").append(System.lineSeparator());
		sb.append("</graphml>");

		return sb.toString();
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
		sb.append("\t<node id=\"").append(node.getId()).append("\">");
		sb.append("<data key=\"d6\"><y:ShapeNode>");
		sb.append("<y:NodeLabel>").append(escape(attributes.getLabel())).append("</y:NodeLabel>");
		sb.append("<y:Fill color=\"").append(mapColorToString(attributes.getFillColor()))
				.append("\" transparent=\"false\"/>");
		sb.append("<y:BorderStyle");
		sb.append(" color=\"").append(mapColorToString(attributes.getLineColor())).append('\"');
		final String style = mapLineStyleToString(attributes.getLineStyle());
		if (!"".equals(style)) {
			sb.append(" type=\"").append(style).append('\"');
		}
		// TODO: peripheries
		sb.append("/>");
		sb.append("<y:Shape type=\"").append(mapShapeToString(attributes.getShape()))
				.append("\"/></y:ShapeNode></data></node>").append(System.lineSeparator());
	}

	private void printCompositeNode(final CompositeNode node, final StringBuilder sb) {
		final NodeAttributes attributes = node.getAttributes();
		sb.append("<node id=\"").append(node.getId()).append("\">").append(System.lineSeparator());
		sb.append("\t<data key=\"d6\"><y:ProxyAutoBoundsNode><y:Realizers active=\"0\"><y:GroupNode>")
				.append(System.lineSeparator());
		sb.append("\t<y:NodeLabel modelName=\"internal\" modelPosition=\"t\">").append(escape(attributes.getLabel()))
				.append("</y:NodeLabel>").append(System.lineSeparator());
		sb.append("\t<y:Fill color=\"").append(mapColorToString(attributes.getFillColor()))
				.append("\" transparent=\"false\"/>").append(System.lineSeparator());
		sb.append("<y:BorderStyle");
		sb.append(" color=\"").append(mapColorToString(attributes.getLineColor())).append('\"');
		final String style = mapLineStyleToString(attributes.getLineStyle());
		if (!"".equals(style)) {
			sb.append(" type=\"").append(style).append('\"');
		}

		// TODO: peripheries
		sb.append("/>");

		sb.append("\t<y:Shape type=\"").append(mapShapeToString(attributes.getShape()))
				.append("\"/></y:GroupNode></y:Realizers></y:ProxyAutoBoundsNode>").append(System.lineSeparator());
		sb.append("\t</data>").append(System.lineSeparator());
		sb.append("\t<graph edgedefault=\"directed\" id=\"").append(node.getId()).append(":\">");
		for (final Node child : node.getChildren()) {
			printNode(child, sb);
		}
		sb.append("\t</graph>").append(System.lineSeparator()).append("</node>").append(System.lineSeparator());
	}

	private void printEdges(final Node node, final StringBuilder sb) {
		for (final Edge edge : node.getOutEdges()) {
			final EdgeAttributes attributes = edge.getAttributes();
			sb.append("\t<edge id=\"").append(edge.hashCode()).append("\" source=\"").append(edge.getSource().getId())
					.append("\" target=\"").append(edge.getTarget().getId()).append("\">");
			sb.append("<data key=\"d9\"><y:PolyLineEdge><y:LineStyle color=\"")
					.append(mapColorToString(attributes.getColor())).append('\"');
			final String style = mapLineStyleToString(attributes.getLineStyle());
			if (!"".equals(style)) {
				sb.append(" type=\"").append(style).append('\"');
			}
			sb.append("/>");
			sb.append("<y:Arrows source=\"none\" target=\"standard\"/>");
			sb.append("<y:EdgeLabel>").append(attributes.getLabel()).append("</y:EdgeLabel>");
			sb.append("</y:PolyLineEdge></data></edge>");
			sb.append(System.lineSeparator());
		}
	}

	private static String escape(final String str) {
		return str.replace("<", "&lt;").replace(">", "&lt;");

	}

	private String mapColorToString(final Color color) {
		return String.format("#%02X%02X%02X", color.getRed(), color.getGreen(), color.getBlue());
	}

	private String mapLineStyleToString(final LineStyle lineStyle) {
		switch (lineStyle) {
			case DASHED:
				return "dashed";
			case DOTTED:
				return "dotted";
			case NORMAL:
				return "";
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
