package hu.bme.mit.theta.common.visualization;

import java.awt.Color;

import hu.bme.mit.theta.common.visualization.writer.YedWriter;

public class VisualizationTest {

	public static void main(final String[] args) {
		final Graph g = new Graph("g", "A graph");
		g.addNode("n1", NodeAttributes.builder().fillColor(Color.RED).label("1").build());
		g.addNode("n2", NodeAttributes.builder().lineColor(Color.BLUE).label("2").build());
		g.addNode("n3", NodeAttributes.builder().lineStyle(LineStyle.DASHED).label("3").build());
		g.addNode("n4", NodeAttributes.builder().peripheries(3).label("4").shape(Shape.RECTANGLE).build());

		g.addCompositeNode("c1", NodeAttributes.builder().label("cluster1").lineStyle(LineStyle.DOTTED)
				.shape(Shape.RECTANGLE).peripheries(2).build());
		g.addCompositeNode("c2", NodeAttributes.builder().label("cluster2").shape(Shape.RECTANGLE).build());

		g.setChild("c1", "n1");
		g.setChild("c1", "n2");
		g.setChild("c2", "n3");
		g.setChild("c1", "c2");

		g.addEdge("n1", "n2", EdgeAttributes.builder().color(Color.YELLOW).label("e").build());
		g.addEdge("n2", "n3", EdgeAttributes.builder().lineStyle(LineStyle.DASHED).build());
		g.addEdge("n4", "n3", EdgeAttributes.builder().lineStyle(LineStyle.DOTTED).build());

		System.out.println(new YedWriter().writeString(g));
	}
}
