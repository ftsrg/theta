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

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;

import hu.bme.mit.theta.common.visualization.Graph;

/**
 * Base class for writing graphs.
 */
public abstract class AbstractGraphWriter implements GraphWriter {

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
