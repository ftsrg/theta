package hu.bme.mit.theta.common.visualization.writer;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;

import hu.bme.mit.theta.common.visualization.Graph;

/**
 * Base class for writing graphs.
 */
abstract class AbstractGraphWriter implements GraphWriter {

	@Override
	public abstract String writeString(Graph graph);

	@Override
	public final void writeFile(final Graph graph, final String fileName) throws FileNotFoundException {
		final File file = new File(fileName);
		PrintWriter printWriter = null;
		try {
			printWriter = new PrintWriter(file);
			final String graphAsString = writeString(graph);
			printWriter.write(graphAsString);
		} catch (final FileNotFoundException e) {
			throw e;
		} finally {
			if (printWriter != null) {
				printWriter.close();
			}
		}
	}

}
