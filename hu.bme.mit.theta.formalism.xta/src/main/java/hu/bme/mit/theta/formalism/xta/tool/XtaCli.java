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
package hu.bme.mit.theta.formalism.xta.tool;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;

import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.TraceVisualizer;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.table.impl.BasicTableWriter;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.lazy.LazyXtaStatistics;
import hu.bme.mit.theta.formalism.xta.dsl.XtaDslManager;
import hu.bme.mit.theta.formalism.xta.tool.XtaCheckerBuilder.Algorithm;

public final class XtaCli {
	private static final String JAR_NAME = "theta-xta.jar";
	private final String[] args;
	private final TableWriter writer;

	@Parameter(names = { "--algorithm" }, description = "Algorithm", required = true)
	Algorithm algorithm;

	@Parameter(names = { "--model" }, description = "Path of the input model", required = true)
	String model;

	@Parameter(names = { "--search" }, description = "Search strategy", required = true)
	SearchStrategy searchStrategy;

	@Parameter(names = { "--benchmark" }, description = "Benchmark mode (only print metrics)")
	Boolean benchmarkMode = false;

	@Parameter(names = { "--visualize" }, description = "Write proof or counterexample to file in dot format")
	String dotfile = null;

	@Parameter(names = { "--header" }, description = "Print only a header (for benchmarks)", help = true)
	boolean headerOnly = false;

	public XtaCli(final String[] args) {
		this.args = args;
		this.writer = new BasicTableWriter(System.out, ",", "\"", "\"");
	}

	public static void main(final String[] args) {
		final XtaCli mainApp = new XtaCli(args);
		mainApp.run();
	}

	private void run() {
		try {
			JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(args);
		} catch (final ParameterException ex) {
			System.out.println("Invalid parameters, details:");
			System.out.println(ex.getMessage());
			ex.usage();
			return;
		}

		if (headerOnly) {
			printHeader();
			return;
		}

		try {
			final XtaSystem xta = loadModel();
			final SafetyChecker<?, ?, UnitPrec> checker = XtaCheckerBuilder.build(algorithm, searchStrategy, xta);
			final SafetyResult<?, ?> result = checker.check(UnitPrec.getInstance());
			printResult(result);
			if (dotfile != null) {
				writeVisualStatus(result, dotfile);
			}
		} catch (final Throwable ex) {
			printError(ex);
		}
		if (benchmarkMode) {
			writer.newRow();
		}
	}

	private void printHeader() {
		writer.cell("Result");
		writer.cell("AlgorithmTimeInMs");
		writer.cell("RefinementTimeInMs");
		writer.cell("InterpolationTimeInMs");
		writer.cell("RefinementSteps");
		writer.cell("ArgDepth");
		writer.cell("ArgNodes");
		writer.cell("ArgNodesFeasible");
		writer.cell("ArgNodesExpanded");
		writer.cell("DiscreteStatesExpanded");
		writer.newRow();
	}

	private XtaSystem loadModel() throws IOException {
		final InputStream inputStream = new FileInputStream(model);
		return XtaDslManager.createSystem(inputStream);
	}

	private void printResult(final SafetyResult<?, ?> result) {
		final LazyXtaStatistics stats = (LazyXtaStatistics) result.getStats().get();

		if (benchmarkMode) {
			writer.cell(result.isSafe());
			writer.cell(stats.getAlgorithmTimeInMs());
			writer.cell(stats.getRefinementTimeInMs());
			writer.cell(stats.getInterpolationTimeInMs());
			writer.cell(stats.getRefinementSteps());
			writer.cell(stats.getArgDepth());
			writer.cell(stats.getArgNodes());
			writer.cell(stats.getArgNodesFeasible());
			writer.cell(stats.getArgNodesExpanded());
			writer.cell(stats.getDiscreteStatesExpanded());
		} else {
			System.out.println(stats.toString());
		}
	}

	private void printError(final Throwable ex) {
		final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
		if (benchmarkMode) {
			writer.cell("[EX] " + ex.getClass().getSimpleName() + message);
		} else {
			System.out.println("Exception occured: " + ex.getClass().getSimpleName());
			System.out.println("Message: " + ex.getMessage());
		}
	}

	private void writeVisualStatus(final SafetyResult<?, ?> status, final String filename)
			throws FileNotFoundException {
		final Graph graph = status.isSafe() ? ArgVisualizer.getDefault().visualize(status.asSafe().getArg())
				: TraceVisualizer.getDefault().visualize(status.asUnsafe().getTrace());
		GraphvizWriter.getInstance().writeFile(graph, filename);
	}

}
