package hu.bme.mit.theta.common.visualization.writer;

import java.io.FileNotFoundException;

import hu.bme.mit.theta.common.visualization.Graph;

/**
 * Inteface for writing graphs to strings and files.
 */
public interface GraphWriter {

	String writeString(Graph graph);

	void writeFile(Graph graph, String fileName) throws FileNotFoundException;
}
