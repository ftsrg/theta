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
package hu.bme.mit.theta.cfa.cfa2dot;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.cfa.analysis.utils.CfaVisualizer;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;

public final class CfaToDotMain {
	private static final String JAR_NAME = "theta-cfa2dot.jar";
	private final String[] args;

	@Parameter(names = {"-c", "--cfa"}, description = "Path of the input cfa", required = true)
	String cfapath;

	@Parameter(names = {"-d", "--dot"}, description = "Path of the output dot", required = false)
	String dotpath;

	public CfaToDotMain(final String[] args) {
		this.args = args;
	}

	public static void main(final String[] args) {
		final CfaToDotMain mainApp = new CfaToDotMain(args);
		mainApp.run();
	}

	private void run() {
		try {
			JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(args);
		} catch (final ParameterException ex) {
			System.out.println(ex.getMessage());
			ex.usage();
			return;
		}

		try {
			final CFA cfa = loadModel(cfapath);
			final Graph graph = CfaVisualizer.visualize(cfa);
			if (dotpath == null) {
				dotpath = cfapath.substring(0, cfapath.lastIndexOf('.')) + ".dot";
			}
			GraphvizWriter.getInstance().writeFile(graph, dotpath);
			return;
		} catch (final Throwable ex) {
			printError(ex);
		}

	}

	private static CFA loadModel(final String path) throws IOException {
		final InputStream inputStream = new FileInputStream(path);
		final CFA cfa = CfaDslManager.createCfa(inputStream);
		return cfa;
	}

	private static void printError(final Throwable ex) {
		final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
		System.out.println("Exception occured: " + ex.getClass().getSimpleName());
		System.out.println("Message: " + message);
	}

}
