package hu.bme.mit.theta.tools.sts;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarStatistics;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.table.impl.SimpleTableWriter;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.StsUtils;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.StsSpec;
import hu.bme.mit.theta.frontend.aiger.impl.AigerParserSimple;
import hu.bme.mit.theta.tools.Configuration;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Domain;
import hu.bme.mit.theta.tools.ConfigurationBuilder.PredSplit;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Refinement;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Search;
import hu.bme.mit.theta.tools.sts.StsConfigurationBuilder.InitPrec;

/**
 * A command line interface for running a CEGAR configuration on an STS.
 */
public class StsMain {
	private static final String JAR_NAME = "theta-sts.jar";
	private final String[] args;
	private final TableWriter tableWriter;

	@Parameter(names = { "-m", "--model" }, description = "Path of the input model", required = true)
	String model;

	@Parameter(names = { "-p", "--property" }, description = "Property to be verified", required = true)
	String property;

	@Parameter(names = { "-d", "--domain" }, description = "Abstract domain", required = true)
	Domain domain;

	@Parameter(names = { "-r", "--refinement" }, description = "Refinement strategy", required = true)
	Refinement refinement;

	@Parameter(names = { "-i", "--initprec" }, description = "Initial precision")
	InitPrec initPrec = InitPrec.EMPTY;

	@Parameter(names = { "-s", "--search" }, description = "Search strategy")
	Search search = Search.BFS;

	@Parameter(names = { "-ps", "--predsplit" }, description = "Predicate splitting")
	PredSplit predSplit = PredSplit.WHOLE;

	@Parameter(names = { "-e", "--expected" }, description = "Expected result", arity = 1)
	Boolean expected;

	@Parameter(names = { "-ll", "--loglevel" }, description = "Detailedness of logging")
	Integer logLevel = 1;

	@Parameter(names = { "-bm", "--benchmark" }, description = "Benchmark mode (only print metrics)")
	Boolean benchmarkMode = false;

	private Logger logger;

	public StsMain(final String[] args) {
		this.args = args;
		tableWriter = new SimpleTableWriter(System.out, ",", "\"", "\"");
	}

	public static void main(final String[] args) {
		final StsMain mainApp = new StsMain(args);
		mainApp.run();
	}

	private void run() {
		if (calledWithHeaderArg()) {
			printHeader();
			return;
		}
		try {
			final JCommander cmd = JCommander.newBuilder().addObject(this).build();
			cmd.setProgramName(JAR_NAME);
			cmd.parse(args);
			logger = benchmarkMode ? NullLogger.getInstance() : new ConsoleLogger(logLevel);
		} catch (final ParameterException ex) {
			System.out.println(ex.getMessage());
			ex.usage();
			return;
		}
		try {
			final STS sts = loadModel();
			final Configuration<?, ?, ?> configuration = buildConfiguration(sts);
			final SafetyResult<?, ?> status = configuration.check();
			checkResult(status);
			printResult(status, sts);
		} catch (final Throwable ex) {
			printError(ex);
		}
		if (benchmarkMode) {
			tableWriter.newRow();
		}
	}

	private boolean calledWithHeaderArg() {
		return args.length == 1 && "--header".equals(args[0]);
	}

	private void printHeader() {
		final String[] header = new String[] { "Result", "TimeMs", "Iterations", "ArgSize", "ArgDepth",
				"ArgMeanBranchFactor", "CexLen", "Vars", "Size" };
		for (final String str : header) {
			tableWriter.cell(str);
		}
		tableWriter.newRow();
	}

	private STS loadModel() throws IOException {
		if (model.endsWith(".aag")) {
			return new AigerParserSimple().parse(model);
		} else if (model.endsWith(".system")) {
			final InputStream inputStream = new FileInputStream(model);
			final StsSpec spec = StsDslManager.createStsSpec(inputStream);
			return StsUtils.eliminateIte(spec.createProp(property));
		} else {
			throw new IOException("Unknown format");
		}
	}

	private Configuration<?, ?, ?> buildConfiguration(final STS sts) {
		return new StsConfigurationBuilder(domain, refinement).initPrec(initPrec).search(search).predSplit(predSplit)
				.logger(logger).build(sts);
	}

	private void checkResult(final SafetyResult<?, ?> status) throws Exception {
		if (expected != null && !expected.equals(status.isSafe())) {
			throw new Exception("Expected safe = " + expected + " but was " + status.isSafe());
		}
	}

	private void printResult(final SafetyResult<?, ?> status, final STS sts) {
		final CegarStatistics stats = (CegarStatistics) status.getStats().get();
		if (benchmarkMode) {
			tableWriter.cell(status.isSafe());
			tableWriter.cell(stats.getElapsedMillis());
			tableWriter.cell(stats.getIterations());
			tableWriter.cell(status.getArg().size());
			tableWriter.cell(status.getArg().getDepth());
			tableWriter.cell(status.getArg().getMeanBranchingFactor());
			if (status.isUnsafe()) {
				tableWriter.cell(status.asUnsafe().getTrace().length() + "");
			} else {
				tableWriter.cell("");
			}
			tableWriter.cell(sts.getVars().size());
			tableWriter.cell(ExprUtils.nodeCountSize(BoolExprs.And(sts.getInit(), sts.getTrans())));
		}
	}

	private void printError(final Throwable ex) {
		final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
		if (benchmarkMode) {
			tableWriter.cell("[EX] " + ex.getClass().getSimpleName() + message);
		} else {
			logger.writeln("Exception occured: " + ex.getClass().getSimpleName(), 0);
			logger.writeln("Message: " + ex.getMessage(), 0, 1);
		}
	}
}
