package hu.bme.mit.inf.theta.cegar.common.utils.visualization;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;

import hu.bme.mit.inf.theta.cegar.common.utils.visualization.graph.ClusterNode;
import hu.bme.mit.inf.theta.cegar.common.utils.visualization.graph.Graph;
import hu.bme.mit.inf.theta.cegar.common.utils.visualization.graph.Node;

/**
 * GraphViz visualizer
 * 
 * @author Akos
 */
public class GraphVizVisualizer implements Visualizer {

	private final String path; // Folder to put graphs
	private final String fileNamePrefix; // Prefix for generated file names
	private int counter; // Counter for file names
	private final int minLevel; // Only log below this level
	private final boolean convertToPng;

	/**
	 * Constructor
	 * 
	 * @param path
	 *            Folder to put graphs
	 * @param fileNamePrefix
	 *            Prefix for generated file names
	 * @param minLevel
	 *            Only log below this level
	 */
	public GraphVizVisualizer(final String path, final String fileNamePrefix, final int minLevel) {
		this(path, fileNamePrefix, minLevel, false);
	}

	/**
	 * Constructor. If convertToPng is set to true, the generated .dot files are
	 * converted to .png, and deleted. This requires dot.exe to be added to
	 * PATH.
	 * 
	 * @param path
	 *            Folder to put graphs
	 * @param fileNamePrefix
	 *            Prefix for generated file names
	 * @param minLevel
	 *            Only log below this level
	 * @param convertToPng
	 *            Convert generated graph to .png image
	 */
	public GraphVizVisualizer(final String path, final String fileNamePrefix, final int minLevel, final boolean convertToPng) {
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
	public String visualize(final Graph graph) {
		PrintWriter pw = null;
		try {
			final File file = new File(path, fileNamePrefix + "_" + (counter++) + ".dot");
			pw = new PrintWriter(file);
			pw.println("digraph " + graph.getId() + " {");
			for (final Node node : graph.getNodes()) {
				if (node.getClass().equals(ClusterNode.class))
					visualize((ClusterNode) node, pw);
				else
					visualize(node, pw);
			}
			for (final Node node : graph.getNodes())
				visualizeArcs(node, pw);
			pw.println("}");
			pw.close();

			// Convert .dot to .png and remove .dot
			if (convertToPng) {
				final String baseName = file.getAbsolutePath().substring(0, file.getAbsolutePath().lastIndexOf('.'));
				final Process proc = Runtime.getRuntime().exec("dot.exe -Tpng \"" + baseName + ".dot\" -o \"" + baseName + ".png\"");
				proc.waitFor();
				file.delete();
				return baseName + ".png";
			} else {
				return file.getAbsolutePath();
			}
		} catch (IOException | InterruptedException e) {
			System.out.println("Graph generation failed " + e.getMessage());
		} finally {
			if (pw != null)
				pw.close();
		}
		return null;
	}

	private void visualize(final Node node, final PrintWriter pw) {
		String style = node.getLineStyle();
		if (!node.getFillColor().equals("")) {
			if (!style.equals(""))
				style += ",filled";
			else
				style = "filled";
		}
		pw.println("\t\t" + node.getId() + " [label=\"" + node.getLabel().replace("\n", "\\n") + "\"" + (node.isInitial() ? ", peripheries=2" : "")
				+ (style.equals("") ? "" : ",style=\"" + style + "\"") + (node.getFillColor().equals("") ? "" : ",fillcolor=" + node.getFillColor())
				+ (node.getColor().equals("") ? "" : ",color=" + node.getColor()) + "];");
	}

	private void visualize(final ClusterNode node, final PrintWriter pw) {
		pw.println("\tsubgraph " + node.getId() + " {");
		if (!node.getColor().equals(""))
			pw.println("\t\tcolor=" + node.getColor() + ";");
		if (!node.getFillColor().equals(""))
			pw.println("\t\tstyle=filled;\n\t\tfillcolor=" + node.getFillColor() + ";");
		pw.println("\t\tlabel=\"" + node.getLabel().replace("\n", "\\n") + "\";");
		if (node.isInitial())
			pw.println("\t\tpenwidth=2.0;");
		for (final Node sub : node.getSubNodes()) {
			if (sub.getClass().equals(ClusterNode.class))
				visualize((ClusterNode) sub, pw);
			else
				visualize(sub, pw);
		}
		pw.println("\t}");
	}

	private void visualizeArcs(final Node node, final PrintWriter pw) {
		// To the best of my knowledge, GraphViz does not support edges between
		// clusters, thus such edges are ignored
		if (node instanceof ClusterNode) {
			for (final Node sub : ((ClusterNode) node).getSubNodes())
				visualizeArcs(sub, pw);
		} else {
			for (final String succId : node.getSuccessors())
				pw.println("\t\t" + node.getId() + " -> " + succId + (node.getArcColor(succId).equals("") ? "" : " [color=" + node.getArcColor(succId) + "]")
						+ ";");
		}
	}

}
