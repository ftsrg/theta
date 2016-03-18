package hu.bme.mit.inf.ttmc.cegar.common.utils.visualization;

import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.ClusterNode;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.Graph;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.Node;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
/**
 * GraphViz visualizer
 * @author Akos
 */
public class GraphVizVisualizer implements IVisualizer {
	
	private String path;           // Folder to put graphs
	private String fileNamePrefix; // Prefix for generated file names
	private int counter;           // Counter for file names
	private int minLevel;          // Only log below this level
	private boolean convertToPng;
	
	/**
	 * Constructor
	 * @param path Folder to put graphs
	 * @param fileNamePrefix Prefix for generated file names
	 * @param minLevel Only log below this level
	 */
	public GraphVizVisualizer(String path, String fileNamePrefix, int minLevel) {
		this(path, fileNamePrefix, minLevel, false);
	}
	
	/**
	 * Constructor. If convertToPng is set to true, the generated .dot files are converted
	 * to .png, and deleted. This requires dot.exe to be added to PATH.
	 * @param path Folder to put graphs
	 * @param fileNamePrefix Prefix for generated file names
	 * @param minLevel Only log below this level
	 * @param convertToPng Convert generated graph to .png image
	 */
	public GraphVizVisualizer(String path, String fileNamePrefix, int minLevel, boolean convertToPng){
		this.path = path;
		this.fileNamePrefix = fileNamePrefix;
		this.counter = 0;
		this.minLevel = minLevel;
		this.convertToPng = convertToPng;
	}
	
	@Override
	public int getMinLevel() {
		return minLevel;
	}

	@Override
	public String visualize(Graph graph) {
		PrintWriter pw = null;
		try {
			File file = new File(path, fileNamePrefix + "_" + (counter++) + ".dot");
			pw = new PrintWriter(file);
			pw.println("digraph " + graph.getId() + " {");
			for (Node node : graph.getNodes()) {
				if(node.getClass().equals(ClusterNode.class)) visualize((ClusterNode)node, pw);
				else visualize(node, pw);
			}
			for (Node node : graph.getNodes()) visualizeArcs(node, pw);
			pw.println("}");
			pw.close();

			// Convert .dot to .png and remove .dot
			if (convertToPng) {
				String baseName = file.getAbsolutePath().substring(0, file.getAbsolutePath().lastIndexOf('.'));
				Process proc = Runtime.getRuntime().exec("dot.exe -Tpng \"" + baseName + ".dot\" -o \"" + baseName + ".png\"");
				proc.waitFor();
				file.delete();
				return baseName + ".png";
			} else {
				return file.getAbsolutePath();
			}
		}
		catch (IOException | InterruptedException e) {
			System.out.println("Graph generation failed " + e.getMessage());
		}
		finally{
			if (pw != null) pw.close();
		}
		return null;
	}
	
	private void visualize(Node node, PrintWriter pw){
		String style = node.getLineStyle();
		if (!node.getFillColor().equals("")) {
			if (!style.equals("")) style += ",filled";
			else style = "filled";
		}
		pw.println("\t\t" + node.getId() + " [label=\"" + node.getLabel().replace("\n", "\\n") + "\""
				+ (node.isInitial() ? ", peripheries=2" : "")
				+ (style.equals("") ? "" : ",style=\"" + style + "\"")
				+ (node.getFillColor().equals("") ? "" : ",fillcolor=" + node.getFillColor())
				+ (node.getColor().equals("") ? "" : ",color=" + node.getColor())
				+ "];");
	}
	
	private void visualize(ClusterNode node, PrintWriter pw){
		pw.println("\tsubgraph " + node.getId() + " {");
		if(!node.getColor().equals("")) pw.println("\t\tcolor=" + node.getColor() + ";");
		if(!node.getFillColor().equals("")) pw.println("\t\tstyle=filled;\n\t\tfillcolor=" + node.getFillColor() + ";");
		pw.println("\t\tlabel=\"" + node.getLabel().replace("\n", "\\n") + "\";");
		if(node.isInitial()) pw.println("\t\tpenwidth=2.0;");
		for (Node sub : node.getSubNodes()) {
			if(sub.getClass().equals(ClusterNode.class)) visualize((ClusterNode)sub, pw);
			else visualize(sub, pw);
		}
		pw.println("\t}");
	}
	
	private void visualizeArcs(Node node, PrintWriter pw){
		// To the best of my knowledge, GraphViz does not support edges between
		// clusters, thus such edges are ignored
		if (node instanceof ClusterNode) {
			for (Node sub : ((ClusterNode)node).getSubNodes()) visualizeArcs(sub, pw);
		} else {
			for(String succId : node.getSuccessors())
				pw.println("\t\t" + node.getId() + " -> " + succId
						+ (node.getArcColor(succId).equals("") ? "" : " [color=" + node.getArcColor(succId) + "]")
						+ ";");
		}
	}
	
}
