package hu.bme.mit.theta.splittingcegar.ui;

import static hu.bme.mit.theta.common.Utils.singleElementOf;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.common.logging.impl.FileLogger;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.StsSpec;
import hu.bme.mit.theta.frontend.aiger.impl.AigerParserSimple;
import hu.bme.mit.theta.splittingcegar.clustered.ClusteredCEGARBuilder;
import hu.bme.mit.theta.splittingcegar.common.CEGARLoop;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.GraphVizVisualizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.YedVisualizer;
import hu.bme.mit.theta.splittingcegar.interpolating.InterpolatingCEGARBuilder;
import hu.bme.mit.theta.splittingcegar.interpolating.InterpolatingCEGARBuilder.InterpolationMethod;
import hu.bme.mit.theta.splittingcegar.visible.VisibleCEGARBuilder;
import hu.bme.mit.theta.splittingcegar.visible.VisibleCEGARBuilder.VarCollectionMethod;

public class CLI {

	private enum Options {
		Algorithm, Model, Log, LogLevel, VisPath, VisType, VisLevel, UseCNF, CollectFromCond, CollectFromProp, InterpolationMethod, VarCollectionMethod, IncrementalModelChecking, ExplicitVars, Debug
	};

	public static void main(final String[] args) {
		// Parse arguments
		final Map<Options, String> parsedArgs = parseArgs(args);

		CEGARLoop cegar = null;
		String model = null;
		String algorithm = null;
		Logger logger = null;
		Visualizer visualizer = null;

		// Get model path
		if (!parsedArgs.containsKey(Options.Model))
			error("Model is not specified.");
		model = parsedArgs.get(Options.Model);

		// Get algorithm name
		if (!parsedArgs.containsKey(Options.Algorithm))
			error("Algorithm is not specified.");
		algorithm = parsedArgs.get(Options.Algorithm);

		// Get logging type and level
		if (parsedArgs.containsKey(Options.Log)) {
			int logLevel = 100;
			if (parsedArgs.containsKey(Options.LogLevel)) {
				try {
					logLevel = Integer.parseInt(parsedArgs.get(Options.LogLevel));
				} catch (final Exception ex) {
					error("Log level must be an integer.");
				}
			}
			switch (parsedArgs.get(Options.Log)) {
			case "console":
				logger = new ConsoleLogger(logLevel);
				break;
			default:
				try {
					logger = new FileLogger(logLevel, parsedArgs.get(Options.Log), true, false);
				} catch (final FileNotFoundException ex) {
					error("File " + parsedArgs.get(Options.Log) + " cannot be opened.");
				}
				break;
			}
		}

		final String dateStr = new SimpleDateFormat("yyyyMMddHHmmssSSS").format(new Date());

		// Debugging
		Visualizer debugVisualizer = null;
		if (parsedArgs.containsKey(Options.Debug) && parsedArgs.get(Options.Debug).equals("true"))
			debugVisualizer = new GraphVizVisualizer(".", "debug_" + dateStr, 100);

		// Get visualization path, type and level
		if (parsedArgs.containsKey(Options.VisPath)) {
			int visLevel = 100;
			if (parsedArgs.containsKey(Options.VisLevel)) {
				try {
					visLevel = Integer.parseInt(parsedArgs.get(Options.VisLevel));
				} catch (final Exception ex) {
					error("Visualization level must be an integer.");
				}
			}
			final String visPath = parsedArgs.get(Options.VisPath);
			if (parsedArgs.containsKey(Options.VisType)) {
				switch (parsedArgs.get(Options.VisType)) {
				case "yed":
					visualizer = new YedVisualizer(visPath, dateStr, visLevel);
					break;
				case "graphviz":
					visualizer = new GraphVizVisualizer(visPath, dateStr, visLevel);
					break;
				default:
					warning("Unknown visualizer: " + parsedArgs.get(Options.VisType));
					break;
				}
			}
		}

		// Create algorithms and parse specific options
		if ("clustered".equals(algorithm)) { // Clustered
			cegar = new ClusteredCEGARBuilder().visualizer(visualizer).debug(debugVisualizer).build();
		} else if ("visible".equals(algorithm)) { // Visible
			final VisibleCEGARBuilder builder = new VisibleCEGARBuilder().logger(logger).debug(debugVisualizer)
					.visualizer(visualizer);
			// CNF option
			if (parsedArgs.containsKey(Options.UseCNF))
				builder.useCNFTransformation("true".equals(parsedArgs.get(Options.UseCNF)));
			// Variable collection method
			if (parsedArgs.containsKey(Options.VarCollectionMethod)) {
				switch (parsedArgs.get(Options.VarCollectionMethod)) {
				case "craig":
					builder.varCollectionMethod(VarCollectionMethod.CraigItp);
					break;
				case "sequence":
					builder.varCollectionMethod(VarCollectionMethod.SequenceItp);
					break;
				case "unsatcore":
					builder.varCollectionMethod(VarCollectionMethod.UnsatCore);
					break;
				default:
					warning("Unknown interpolation method: " + parsedArgs.get(Options.InterpolationMethod));
					break;
				}
			}
			cegar = builder.build();
		} else if ("interpolating".equals(algorithm)) { // Interpolated
			final InterpolatingCEGARBuilder builder = new InterpolatingCEGARBuilder().logger(logger)
					.debug(debugVisualizer).visualizer(visualizer);
			// CNF option
			if (parsedArgs.containsKey(Options.UseCNF))
				builder.useCNFTransformation("true".equals(parsedArgs.get(Options.UseCNF)));
			// Collect initial predicates from conditions
			if (parsedArgs.containsKey(Options.CollectFromCond))
				builder.collectFromConditions("true".equals(parsedArgs.get(Options.CollectFromCond)));
			// Collect initial predicates from specification
			if (parsedArgs.containsKey(Options.CollectFromProp))
				builder.collectFromSpecification("true".equals(parsedArgs.get(Options.CollectFromProp)));
			// Incremental model checking
			if (parsedArgs.containsKey(Options.IncrementalModelChecking))
				builder.incrementalModelChecking("true".equals(parsedArgs.get(Options.IncrementalModelChecking)));
			// Interpolation method
			if (parsedArgs.containsKey(Options.InterpolationMethod)) {
				switch (parsedArgs.get(Options.InterpolationMethod)) {
				case "craig":
					builder.interpolationMethod(InterpolationMethod.Craig);
					break;
				case "sequence":
					builder.interpolationMethod(InterpolationMethod.Sequence);
					break;
				default:
					warning("Unknown interpolation method: " + parsedArgs.get(Options.InterpolationMethod));
					break;
				}
			}
			// Explicit variables
			if (parsedArgs.containsKey(Options.ExplicitVars))
				for (final String explVar : parsedArgs.get(Options.ExplicitVars).split(","))
					builder.explicitVar(explVar);

			cegar = builder.build();
		} else {
			error("Unknown algorithm: " + algorithm);
		}

		STS problem = null;

		// Run algorithm
		try {
			if (model.endsWith(".system")) {
				final InputStream inputStream = new FileInputStream(model);
				final StsSpec stsSpec = StsDslManager.createStsSpec(inputStream);
				problem = singleElementOf(stsSpec.getAllSts());
			} else if (model.endsWith(".aag")) {
				problem = new AigerParserSimple().parse(model);
			}
		} catch (final Exception ex) {
			error("Could not load model: " + ex.getMessage());
		}
		System.out.println("Executing " + cegar);
		cegar.check(problem);
	}

	private static Map<Options, String> parseArgs(final String[] args) {
		final Map<Options, String> parsedArgs = new HashMap<>();
		if (args.length % 2 != 0)
			error("Options and arguments are not in pairs.");

		@SuppressWarnings("serial")
		final Map<String, Options> supportedArgs = new HashMap<String, Options>() {
			{
				put("a", Options.Algorithm);
				put("m", Options.Model);
				put("l", Options.Log);
				put("ll", Options.LogLevel);
				put("vp", Options.VisPath);
				put("vl", Options.VisLevel);
				put("vt", Options.VisType);
				put("cnf", Options.UseCNF);
				put("cc", Options.CollectFromCond);
				put("cp", Options.CollectFromProp);
				put("im", Options.InterpolationMethod);
				put("imc", Options.IncrementalModelChecking);
				put("ex", Options.ExplicitVars);
				put("dbg", Options.Debug);
			}
		};

		for (int i = 0; i < args.length; i += 2) {
			if (supportedArgs.containsKey(args[i].substring(1))) {
				if (parsedArgs.containsKey(supportedArgs.get(args[i].substring(1))))
					warning("Argument " + args[i] + " is ignored because it was already specified.");
				else
					parsedArgs.put(supportedArgs.get(args[i].substring(1)), args[i + 1].toLowerCase());
			} else {
				warning("Unknown argument: " + args[i]);
			}
		}

		return parsedArgs;
	}

	private static void error(final String message) {
		System.out.println("ERROR: " + message);
		System.exit(0);
	}

	private static void warning(final String message) {
		System.out.println("WARNING: " + message);
	}
}
