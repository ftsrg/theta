package hu.bme.mit.theta.splittingcegar.common.utils.visualization;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.ClusterNode;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.Graph;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.Node;

/**
 * yED visualizer
 * @author Akos
 */
public class YedVisualizer implements Visualizer {
	private String path;           // Folder to put graphs
	private String fileNamePrefix; // Prefix for generated file names
	private int counter;           // Counter for file names
	private int minLevel;          // Only log below this level
	
	/**
	 * Constructor
	 * @param path Folder to put graphs
	 * @param fileNamePrefix Prefix for generated file names
	 * @param minLevel Only log below this level
	 */
	public YedVisualizer(String path, String fileNamePrefix, int minLevel){
		this.path = path;
		this.fileNamePrefix = fileNamePrefix;
		this.counter = 0;
		this.minLevel = minLevel;
	}
	
	@Override
	public String visualize(Graph graph) {
		PrintWriter pw = null;
		try {
			File file = new File(path, fileNamePrefix + "_" + (counter++) + ".graphml");
			pw = new PrintWriter(file);
			pw.println("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\r\n" + 
					"<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\"\r\n" + 
					"\txmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"\r\n" + 
					"\txmlns:y=\"http://www.yworks.com/xml/graphml\"\r\n" + 
					"\txmlns:yed=\"http://www.yworks.com/xml/yed/3\"\r\n" + 
					"\txsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns http://www.yworks.com/xml/schema/graphml/1.1/ygraphml.xsd\">");
			pw.println("<key for=\"node\" id=\"d6\" yfiles.type=\"nodegraphics\"/>");
			pw.println("<key for=\"edge\" id=\"d9\" yfiles.type=\"edgegraphics\"/>");
			pw.println("<graph edgedefault=\"directed\" id=\"" + graph.getId() + "\">");
			for (Node node : graph.getNodes()) {
				if(node.getClass().equals(ClusterNode.class)) visualize((ClusterNode)node, pw);
				else visualize(node, pw);
			}
			for (Node node : graph.getNodes()) visualizeArcs(node, pw);
			pw.println("</graph>\r\n</graphml>");
			pw.close();
			return file.getAbsolutePath();
		}
		catch (FileNotFoundException e) {
			System.out.println("Graph generation failed " + e.getMessage());
		}
		finally{
			if (pw != null) pw.close();
		}
		return null;
	}

	private void visualizeArcs(Node node, PrintWriter pw) {
		for(String succId : node.getSuccessors())
			pw.println("\t<edge id=\"" + node.getId() + succId + "\" source=\"" + node.getId() + "\" target=\"" + succId + "\">"
					+ "<data key=\"d9\"><y:PolyLineEdge>"
					+ (node.getArcColor(succId).equals("") ? "" : "<y:LineStyle color=\"" + colorMap.get(node.getArcColor(succId)) + "\"/>")
					+ "<y:Arrows source=\"none\" target=\"standard\"/></y:PolyLineEdge></data></edge>");
		if (node instanceof ClusterNode)
			for (Node sub : ((ClusterNode)node).getSubNodes()) visualizeArcs(sub, pw);
	}

	private void visualize(Node node, PrintWriter pw) {
		pw.println("\t<node id=\"" + node.getId() + "\"><data key=\"d6\"><y:ShapeNode>"
				+ "<y:NodeLabel>" + replaceLabel(node.getLabel()) + "</y:NodeLabel>"
				+ (!node.getFillColor().equals("") ? ("<y:Fill color=\"" + colorMap.get(node.getFillColor()) + "\" transparent=\"false\"/>") : "<y:Fill transparent=\"true\"/>\r\n"));
		if (!node.getColor().equals("") || !node.getLineStyle().equals("") || node.isInitial()) {
			pw.println("<y:BorderStyle"
					+ (node.getColor().equals("") ? "" : " color=\"" + colorMap.get(node.getColor()) + "\"")
					+ (node.getLineStyle().equals("") ? "" : " type=\"" + node.getLineStyle() + "\"")
					+ (node.isInitial() ? " width=\"2.0\"" : "")
					+ "/>");
		}
		pw.println("<y:Shape type=\"ellipse\"/></y:ShapeNode></data></node>");
	}

	private void visualize(ClusterNode node, PrintWriter pw) {
		pw.println("<node id=\"" + node.getId() + "\">\r\n" + 
				"\t<data key=\"d6\"><y:ProxyAutoBoundsNode><y:Realizers active=\"0\"><y:GroupNode>\r\n" + 
				"\t<y:NodeLabel modelName=\"internal\" modelPosition=\"t\">" + replaceLabel(node.getLabel()) + "</y:NodeLabel>\r\n" + 
				(!node.getFillColor().equals("") ? ("\t<y:Fill color=\"" + colorMap.get(node.getFillColor()) + "\" transparent=\"false\"/>\r\n") : "\t<y:Fill transparent=\"true\"/>\r\n"));
		if (!node.getColor().equals("") || !node.getLineStyle().equals("") || node.isInitial()) {
			pw.println("\t<y:BorderStyle"
					+ (node.getColor().equals("") ? "" : " color=\"" + colorMap.get(node.getColor()) + "\"")
					+ (node.getLineStyle().equals("") ? "": " type=\"" + node.getLineStyle() + "\"")
					+ (node.isInitial() ? " width=\"2.0\"" : "")
					+ "/>\r\n");
		}
		pw.println("\t<y:Shape type=\"rectangle\"/></y:GroupNode></y:Realizers></y:ProxyAutoBoundsNode>\r\n" + 
				"\t</data>\r\n" + 
				"\t<graph edgedefault=\"directed\" id=\"" + node.getId() + ":\">");
		for (Node sub : node.getSubNodes()) {
			if(sub.getClass().equals(ClusterNode.class)) visualize((ClusterNode)sub, pw);
			else visualize(sub, pw);
		}
		pw.println("\t</graph>\r\n</node>");
	}

	@Override
	public int getMinLevel() {
		return minLevel;
	}
	
	@SuppressWarnings("serial")
	private static final Map<String, String> colorMap = new HashMap<String, String>(){
		{
		put("red",  "#FF0000");
		put("pink", "#F5A9A9");
		put("white", "#FFFFFF");
		put("black", "#000000");
		put("gray", "#999999");
		put("grey", "#999999");
		}
	};
	
	private String replaceLabel(String label) {
		label = label.replace("<", "&lt;");
		label = label.replace(">", "&lt;");
		return label;
	}

}
