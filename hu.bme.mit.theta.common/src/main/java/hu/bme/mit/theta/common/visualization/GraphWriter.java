package hu.bme.mit.theta.common.visualization;

import java.io.FileNotFoundException;

/**
 * Inteface for writing graphs to strings and files.
 */
public interface GraphWriter {

	String writeString(Graph graph);

	void writeFile(Graph graph, String fileName) throws FileNotFoundException;
}
