package hu.bme.mit.theta.xcfa.analysis.utils;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.WitnessGraphvizWriter;
import hu.bme.mit.theta.common.visualization.writer.WitnessWriter;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.CegarConfiguration;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.CpuTimeKeeper;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.ModelStatistics;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.Result;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaTraceToWitness;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.time.LocalDateTime;
import java.util.Date;
import java.util.TimeZone;

import static com.google.common.base.Preconditions.checkState;

public final class OutputHandler {
	private static String basicFileName;
	private static File model;

	public void writeXcfa(XCFA xcfa) {
		if(outputConfiguration!=OutputOptions.OUTPUT_RESULTS) return;

		checkState(xcfa!=null);
		File xcfafile = new File(basicFileName + ".xcfa");
		try (BufferedWriter bw = new BufferedWriter(new FileWriter(xcfafile))) {
			bw.write(xcfa.toDot());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	static OutputHandler INSTANCE;

	private OutputOptions outputConfiguration = OutputOptions.NONE;

	public static void create(OutputOptions outputConfiguration, File model) {
		if(INSTANCE == null) {
			INSTANCE = new OutputHandler(outputConfiguration, model);
		}
	}

	public static OutputHandler getInstance() {
		checkState(INSTANCE!=null);
		return INSTANCE;
	}

	private OutputHandler(OutputOptions outputConfiguration, File model) {
		this.outputConfiguration = outputConfiguration;
		this.model = model;
	}

	public void createResultsDirectory() {
		checkState(model!=null);
		// portfolio and output-results needs a results directory
		// create the directory only, if needed
		if(outputConfiguration==OutputOptions.OUTPUT_RESULTS) {
			File resultsDir = new File(model + "-" + LocalDateTime.now().toString().replace(":","-") + "-results");
			boolean bool = resultsDir.mkdir();
			if(!bool){
				throw new RuntimeException("Couldn't create results directory");
			}
			basicFileName = resultsDir + "/" + model.getName();
		} else {
			basicFileName = null;
		}
	}

	public void setOutput(OutputOptions outputConfiguration) {
		this.outputConfiguration = outputConfiguration;
	}

	public void writeCounterexamples(SafetyResult<?, ?> status, String refinementSolver) throws Exception {
		if(outputConfiguration==OutputOptions.NONE) return;
		SolverFactory cexSolverFactory = SolverManager.resolveSolverFactory(refinementSolver);
		final Trace<XcfaState<?>, XcfaAction> trace = (Trace<XcfaState<?>, XcfaAction>) status.asUnsafe().getTrace();
		final Trace<XcfaState<ExplState>, XcfaAction> concrTrace = XcfaTraceConcretizer.concretize(trace, cexSolverFactory);

		if(outputConfiguration==OutputOptions.WITNESS_ONLY) {
			Path workdir = FileSystems.getDefault().getPath("").toAbsolutePath();
			File witnessfile = new File(workdir + File.separator + "witness.graphml");

			Graph witnessGraph = XcfaTraceToWitness.buildWitness(concrTrace);
			// TODO make WitnessWriter singleton
			WitnessWriter ww = WitnessWriter.createViolationWitnessWriter(model.getAbsolutePath(), "CHECK( init(main()), LTL(G ! call(reach_error())) )", false);
			try {
				ww.writeFile(witnessGraph, witnessfile.getAbsolutePath());
			} catch (FileNotFoundException e) {
				e.printStackTrace();
			}
		} else if(outputConfiguration==OutputOptions.OUTPUT_RESULTS) {
			File witnessfile = new File(basicFileName + ".witness.graphml");
			File cexfile = new File(basicFileName + ".cex");
			File dotwitnessfile = new File(basicFileName + ".witness.dot");

			PrintWriter printWriter = null;
			try {
				printWriter = new PrintWriter(cexfile);
				printWriter.write(concrTrace.toString());
			} finally {
				if (printWriter != null) {
					printWriter.close();
				}
			}

			Graph witnessGraph = XcfaTraceToWitness.buildWitness(concrTrace);
			// TODO make WitnessWriter singleton
			WitnessWriter ww = WitnessWriter.createViolationWitnessWriter(model.getAbsolutePath(), "CHECK( init(main()), LTL(G ! call(reach_error())) )", false);
			try {
				ww.writeFile(witnessGraph, witnessfile.getAbsolutePath());
			} catch (FileNotFoundException e) {
				e.printStackTrace();
			}
			WitnessGraphvizWriter.getInstance().writeFile(witnessGraph, dotwitnessfile.getAbsolutePath());
		}
		CpuTimeKeeper.saveSolverTimes();
		SolverManager.closeAll();
	}

	public void writeDummyCorrectnessWitness() {
		if(outputConfiguration!=OutputOptions.WITNESS_ONLY) return;
		Path workdir = FileSystems.getDefault().getPath("").toAbsolutePath();
		File witnessfile = new File(workdir + File.separator + "witness.graphml");

		String taskHash = WitnessWriter.createTaskHash(model.getAbsolutePath());
		StringBuilder dummyWitness = new StringBuilder();
		dummyWitness.append("<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">").append(System.lineSeparator()).append(
				"<key id=\"sourcecodelang\" attr.name=\"sourcecodelang\" for=\"graph\"/>").append(System.lineSeparator()).append(
				"<key id=\"witness-type\" attr.name=\"witness-type\" for=\"graph\"/>").append(System.lineSeparator()).append(
				"<key id=\"entry\" attr.name=\"entry\" for=\"node\">").append(System.lineSeparator()).append(
				"<default>false</default>").append(System.lineSeparator()).append(
				"</key>").append(System.lineSeparator()).append(
				"<key id=\"invariant\" attr.name=\"invariant\" for=\"node\">").append(System.lineSeparator()).append(
				"<default>false</default>").append(System.lineSeparator()).append(
				"</key>").append(System.lineSeparator()).append(
				"<key attr.name=\"specification\" attr.type=\"string\" for=\"graph\" id=\"specification\"/>").append(System.lineSeparator()).append(
				"<key attr.name=\"producer\" attr.type=\"string\" for=\"graph\" id=\"producer\"/>").append(System.lineSeparator()).append(
				"<key attr.name=\"programFile\" attr.type=\"string\" for=\"graph\" id=\"programfile\"/>").append(System.lineSeparator()).append(
				"<key attr.name=\"programHash\" attr.type=\"string\" for=\"graph\" id=\"programhash\"/>").append(System.lineSeparator()).append(
				"<key attr.name=\"architecture\" attr.type=\"string\" for=\"graph\" id=\"architecture\"/>").append(System.lineSeparator()).append(
				"<key attr.name=\"creationtime\" attr.type=\"string\" for=\"graph\" id=\"creationtime\"/>").append(System.lineSeparator()).append(
				"<graph edgedefault=\"directed\">").append(System.lineSeparator()).append(
				"<data key=\"witness-type\">correctness_witness</data>").append(System.lineSeparator()).append(
				"<data key=\"producer\">theta</data>").append(System.lineSeparator()).append(
				"<data key=\"specification\">CHECK( init(main()), LTL(G ! call(reach_error())) )</data>").append(System.lineSeparator()).append(
				"<data key=\"sourcecodelang\">C</data>").append(System.lineSeparator()).append(
				"<data key=\"architecture\">32bit</data>").append(System.lineSeparator()).append(
				"<data key=\"programhash\">");
		dummyWitness.append(taskHash);
		dummyWitness.append("</data>").append(System.lineSeparator()).append(
				"<data key=\"creationtime\">");

		TimeZone tz = TimeZone.getTimeZone("UTC");
		DateFormat df = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss'Z'"); // Quoted "Z" to indicate UTC, no timezone offset
		df.setTimeZone(tz);
		String ISOdate = df.format(new Date());

		dummyWitness.append(ISOdate);
		dummyWitness.append("</data>").append(System.lineSeparator()).append(
				"<data key=\"programfile\">");
		dummyWitness.append(model.getName());
		dummyWitness.append("</data>").append(System.lineSeparator()).append(
				"<node id=\"N0\">").append(System.lineSeparator()).append(
				"<data key=\"entry\">true</data>").append(System.lineSeparator()).append(
				"</node>").append(System.lineSeparator()).append(
				"</graph>").append(System.lineSeparator()).append(
				"</graphml>");

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(witnessfile))) {
			bw.write(dummyWitness.toString());
		} catch (IOException ioe) {
			ioe.printStackTrace();
		}
	}

	public void writeInputStatistics(XCFA xcfa) {
		if(outputConfiguration!=OutputOptions.OUTPUT_RESULTS) return;

		checkState(xcfa!=null);
		checkState(model!=null);
		ModelStatistics statistics = ModelStatistics.createXcfaStatistics(xcfa, model.getName());
		File statisticstxtfile = new File(basicFileName + ".statistics.txt");
		File statisticscsvfile = new File(basicFileName + ".csv");
		statistics.writeToCsv(statisticscsvfile);
		statistics.writeToTxt(statisticstxtfile);
	}

	public void writeTxtLine(CegarConfiguration configuration, long timeout, long timeTaken, long cpuTimeTaken, Result result) {
		if(outputConfiguration!=OutputOptions.OUTPUT_RESULTS) return;
		File configurationTxt = new File(basicFileName + ".portfolio.txt");

		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append(configuration);
		stringBuilder.append(", timeout (ms, cputime): ").append(timeout);
		stringBuilder.append(", walltime taken (ms): ").append(timeTaken);
		stringBuilder.append(", cputime taken (s): ").append(cpuTimeTaken);
		stringBuilder.append(", result: ").append(result);
		stringBuilder.append(System.lineSeparator());

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(configurationTxt, true))) {
			bw.write(stringBuilder.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void writeCsvLine(CegarConfiguration configuration, long timeout, long timeTaken, long cpuTimeTaken, Result result) {
		if(outputConfiguration!=OutputOptions.OUTPUT_RESULTS) return;
		File configurationCsv = new File(basicFileName + ".portfolio.csv");

		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append(model.getName()).append("\t");
		stringBuilder.append(configuration).append("\t");
		stringBuilder.append(timeout).append("\t");
		stringBuilder.append(timeTaken).append("\t");
		stringBuilder.append(cpuTimeTaken).append("\t");
		stringBuilder.append(result).append("\t");
		stringBuilder.append(System.lineSeparator());

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(configurationCsv, true))) {
			bw.write(stringBuilder.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	// TODO use XCFA instead of CFA
	/*
	private void writeXcfaWithCex(final XCFA xcfa, final SafetyResult.Unsafe<?, ?> status) throws Exception {
		@SuppressWarnings("unchecked") final Trace<CfaState<?>, CfaAction> trace = (Trace<CfaState<?>, CfaAction>) status.getTrace();
		final Trace<CfaState<ExplState>, CfaAction> concrTrace = CfaTraceConcretizer.concretize(trace, Z3SolverManager.resolveSolverFactory("Z3"));
		Set<String> cexLocations = new LinkedHashSet<>();
		Set<XcfaEdge> cexEdges = new LinkedHashSet<>();
		for (CfaState<ExplState> state : concrTrace.getStates()) {
			cexLocations.add(state.getLoc().getName());
		}
		for (CfaAction action : concrTrace.getActions()) {
			for (CFA.Edge edge : action.getEdges()) {
				Set<Object> xcfaEdges = FrontendMetadata.lookupMetadata("cfaEdge", edge);
				for (Object xcfaEdge : xcfaEdges) {
					XcfaEdge e = (XcfaEdge) xcfaEdge;
					cexEdges.add(e);
				}
			}
		}
		final File file = highlightedxcfafile;
		try (PrintWriter printWriter = new PrintWriter(file)) {
			printWriter.write(xcfa.toDot(cexLocations, cexEdges));
		}
	}
	*/
}
