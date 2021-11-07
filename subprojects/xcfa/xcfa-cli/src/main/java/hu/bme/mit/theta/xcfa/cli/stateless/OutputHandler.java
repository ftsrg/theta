package hu.bme.mit.theta.xcfa.cli.stateless;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.WitnessGraphvizWriter;
import hu.bme.mit.theta.common.visualization.writer.WitnessWriter;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.Portfolio;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaTraceToWitness;
import hu.bme.mit.theta.xcfa.analysis.declarative.XcfaDeclarativeAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.XcfaDeclarativeState;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.time.LocalDateTime;

import static com.google.common.base.Preconditions.checkState;

public class OutputHandler {
	private static String basicFileName;

	enum OutputOptions {
		NONE, WITNESS_ONLY, OUTPUT_RESULTS;
	}

	static OutputHandler INSTANCE;

	private OutputOptions outputConfiguration = OutputOptions.NONE;

	public static void create(OutputOptions outputConfiguration) {
		if(INSTANCE == null) {
			INSTANCE = new OutputHandler(outputConfiguration);
		}
	}

	public static OutputHandler getInstance() {
		checkState(INSTANCE!=null);
		return INSTANCE;
	}

	private OutputHandler(OutputOptions outputConfiguration) {
		this.outputConfiguration = outputConfiguration;
	}

	public void createResultsDirectory(File model) {
		// portfolio and output-results needs a results directory
		File resultsDir = new File(model + "-" + LocalDateTime.now().toString() + "-results");
		// create the directory only, if needed
		if(outputConfiguration==OutputOptions.OUTPUT_RESULTS) {
			boolean bool = resultsDir.mkdir();
			if(!bool){
				throw new RuntimeException("Couldn't create results directory");
			}
		}
		basicFileName = resultsDir + "/" + model.getName();

		/// output results file creation
		// create filenames, if needed
		/*
		if(witnessOnly) {
			Path workdir = FileSystems.getDefault().getPath("").toAbsolutePath();
			witnessfile = new File(workdir + File.separator + "witness.graphml");
		} else if(outputResults) {
			xcfafile = new File(basicFileName + ".xcfa");
			cfafile = new File(basicFileName + ".cfa");
			cexfile = new File(basicFileName + ".cex");
			witnessfile = new File(basicFileName + ".witness.graphml");
			dotwitnessfile = new File(basicFileName + ".witness.dot");
			highlightedxcfafile = new File(basicFileName + ".highlighted.xcfa");
			statisticstxtfile = new File(basicFileName + ".statistics.txt");
			statisticscsvfile = new File(basicFileName + ".csv");
		}

		 */
	}

	public void setOutput(OutputOptions outputConfiguration) {
		this.outputConfiguration = outputConfiguration;
	}

	public void writeCounterexamples(final SafetyResult.Unsafe<?, ?> status, SolverFactory concretizer, File model) throws Exception {
		if(outputConfiguration==OutputOptions.NONE) return;
		final Trace<XcfaDeclarativeState<?>, XcfaDeclarativeAction> trace = (Trace<XcfaDeclarativeState<?>, XcfaDeclarativeAction>) status.getTrace();
		final Trace<XcfaDeclarativeState<ExplState>, XcfaDeclarativeAction> concrTrace = XcfaTraceConcretizer.concretize(trace, concretizer);

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
	}

	public void writeStatistics() {

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
