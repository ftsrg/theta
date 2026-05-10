/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStatistics;
import hu.bme.mit.theta.analysis.expr.ExprMeetStrategy;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.TraceVisualizer;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.exception.NotSolvableException;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.table.BasicTableWriter;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaCheckerConfig;
import hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaCheckerConfigFactory;
import hu.bme.mit.theta.xta.analysis.lazy.*;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import hu.bme.mit.theta.xta.utils.CTLOperatorNotSupportedException;
import hu.bme.mit.theta.xta.utils.MixedDataTimeNotSupportedException;
import java.io.*;

public final class XtaCli {

	public enum Algorithm {
		LAZY, COMBINED
	}

	private static final String JAR_NAME = "theta-xta.jar";
	private final String[] args;
	private final TableWriter writer;

	/// Main parameters

	@Parameter(names = {"--model", "-m"}, description = "Path of the input model", required = true)
	String model;

	@Parameter(names = {"--algorithm"}, description = "The algorithm to use")
	Algorithm algorithm = Algorithm.LAZY;

	/// Lazy algorithm parameters

	@Parameter(names = {"--discreteconcr", "-dc"}, description = "Concrete domain for discrete variables", required = false)
	DataStrategy.ConcrDom concrDataDom = DataStrategy.ConcrDom.EXPL;

	@Parameter(names = {"--discreteabstr", "-da"}, description = "Abstract domain for discrete variables", required = false)
	DataStrategy.AbstrDom abstrDataDom = DataStrategy.AbstrDom.EXPL;

	@Parameter(names = {"--discreteitp", "-di"}, description = "Interpolation strategy for discrete variables", required = false)
	DataStrategy.ItpStrategy dataItpStrategy = DataStrategy.ItpStrategy.BIN_BW;

	@Parameter(names = {"--meet", "-me"}, description = "Meet strategy for expressions", required = false)
	ExprMeetStrategy exprMeetStrategy = ExprMeetStrategy.BASIC;

	/// Combined algorithm parameters

	@Parameter(names = {"--combined-dataDomain"}, description = "Abstract domain for data")
	CombinedLazyCegarXtaCheckerConfigFactory.DataDomain dataDomain = CombinedLazyCegarXtaCheckerConfigFactory.DataDomain.EXPL;

	@Parameter(names = "--combined-predsplit", description = "Predicate splitting (for predicate abstraction)")
	CombinedLazyCegarXtaCheckerConfigFactory.PredSplit predSplit = CombinedLazyCegarXtaCheckerConfigFactory.PredSplit.WHOLE;

	@Parameter(names = "--combined-maxenum", description = "Maximal number of explicitly enumerated successors (0: unlimited)")
	Integer maxEnum = 10;

	@Parameter(names = {"--combined-dataRefinement"}, description = "Data refinement strategy")
	CombinedLazyCegarXtaCheckerConfigFactory.DataRefinement dataRefinement = CombinedLazyCegarXtaCheckerConfigFactory.DataRefinement.SEQ_ITP;

	@Parameter(names = {"--combined-pruneStrategy"}, description = "Strategy for pruning the ARG after refinement")
	PruneStrategy pruneStrategy = PruneStrategy.FULL;

  /// Common algorithm parameters

	@Parameter(names = {"--clock", "-c"}, description = "Refinement strategy for clock variables", required = false)
	ClockStrategy clockStrategy = ClockStrategy.BW_ITP;

	@Parameter(names = {"--search", "-s"}, description = "Search strategy", required = false)
	SearchStrategy searchStrategy = SearchStrategy.BFS;

	/// Common parameters

	@Parameter(names = {"--benchmark", "-b"}, description = "Benchmark mode (only print metrics)")
	Boolean benchmarkMode = false;

	@Parameter(names = {"--visualize", "-v"}, description = "Write proof or counterexample to file in dot format")
	String dotfile = null;

	@Parameter(names = {"--header", "-h"}, description = "Print only a header (for benchmarks)", help = true)
	boolean headerOnly = false;

	@Parameter(names = "--stacktrace", description = "Print full stack trace in case of exception")
	boolean stacktrace = false;

	@Parameter(names = "--loglevel", description = "Detailedness of logging")
	Logger.Level logLevel = Logger.Level.VERBOSE;

	@Parameter(names = "--version", description = "Display version", help = true)
	boolean versionInfo = false;

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

		if (versionInfo) {
			CliUtils.printVersion(System.out);
			return;
		}

    if (headerOnly) {
      LazyStatistics.writeHeader(writer);
      return;
    }

    if (benchmarkMode) {
      logLevel = Logger.Level.DISABLE;
    }

		try {
			final XtaSystem system = loadModel();
      final SafetyResult<? extends ARG<?, ?>, ? extends Trace<? extends State, ? extends Action>>
          result = switch (algorithm) {
              case LAZY -> runLazy(system);
              case COMBINED -> runCombined(system);
          };
      if (dotfile != null) {
        writeVisualStatus(result, dotfile);
      }
		} catch (final Throwable ex) {
			printError(ex);
			System.exit(1);
		}
	}

  private XtaSystem loadModel() {
    try {
      try (InputStream inputStream = new FileInputStream(model)) {
        return XtaDslManager.createSystem(inputStream);
      }
    } catch (CTLOperatorNotSupportedException ex) {
      ex.printStackTrace();
      System.exit(11);
    } catch (MixedDataTimeNotSupportedException ex) {
      ex.printStackTrace();
      System.exit(12);
    } catch (Exception ex) {
      ex.printStackTrace();
      System.exit(10);
    }
    throw new AssertionError();
  }

	private SafetyResult<? extends ARG<?, ?>, ? extends Trace<? extends State, ? extends Action>>
  runLazy(final XtaSystem system) {
		final LazyXtaCheckerConfig<?, ?, ?> config =
        LazyXtaCheckerConfigFactory.create(
            system,
            new ConsoleLogger(logLevel),
            new DataStrategy(concrDataDom, abstrDataDom, dataItpStrategy),
            clockStrategy,
            searchStrategy,
            exprMeetStrategy
        );
    final SafetyResult<? extends ARG<?, ?>, ? extends Trace<? extends State, ? extends Action>>
        result = config.check();
    final LazyStatistics stats = (LazyStatistics) (result.getStats().get());
    printResult(system.getPropertyKind(), result.isSafe(), result.isUnsafe(), stats);
    return result;
	}

	private SafetyResult<? extends ARG<?, ?>, ? extends Trace<? extends State, ? extends Action>>
  runCombined(final XtaSystem system) {
		 final CombinedLazyCegarXtaCheckerConfig<?, ?, ? extends ARG<?, ?>, ? extends Trace<? extends State, ? extends Action>> config =
        CombinedLazyCegarXtaCheckerConfigFactory
            .create(system, new ConsoleLogger(logLevel), Z3LegacySolverFactory.getInstance())
            .dataDomain(dataDomain)
            .maxEnum(maxEnum)
            .predSplit(predSplit)
            .dataRefinement(dataRefinement)
            .clockStrategy(clockStrategy)
            .searchStragegy(searchStrategy)
            .pruneStrategy(pruneStrategy)
            .build();
		try {
			final SafetyResult<? extends ARG<?, ?>, ? extends Trace<? extends State, ? extends Action>>
          result = config.check();
			printResult(system.getPropertyKind(), result.isSafe(), result.isUnsafe(), null);
      return result;
		} catch (NotSolvableException ex) {
			ex.printStackTrace();
			System.exit(9);
      return null;
		}
  }

	private void printResult(final XtaSystem.PropertyKind propertyKind,
                           final boolean isSafe, final boolean isUnsafe,
                           final LazyStatistics lazyStats) {
    if (benchmarkMode && lazyStats != null) {
      lazyStats.writeData(writer);
    }
    if (isSafe) {
			switch (propertyKind) {
				case AG -> System.out.println("(SafetyResult Safe)");
				case EF -> System.out.println("(SafetyResult Unsafe)");
				default -> throw new UnsupportedOperationException();
			}
		} else if (isUnsafe) {
			switch (propertyKind) {
				case AG -> System.out.println("(SafetyResult Unsafe)");
				case EF -> System.out.println("(SafetyResult Safe)");
				default -> throw new UnsupportedOperationException();
			}
		} else {
			throw new UnsupportedOperationException();
		}
	}

  private void printError(final Throwable ex) {
      final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
      if (benchmarkMode) {
          writer.cell("[EX] " + ex.getClass().getSimpleName() + message);
      } else {
          System.out.println(ex.getClass().getSimpleName() + " occurred, message: " + message);
          if (stacktrace) {
              final StringWriter errors = new StringWriter();
              ex.printStackTrace(new PrintWriter(errors));
              System.out.println("Trace:");
              System.out.println(errors);
          } else {
              System.out.println("Use --stacktrace for stack trace");
          }
      }
  }

  private void writeVisualStatus(
      final SafetyResult<? extends ARG<?, ?>, ? extends Trace<? extends State, ? extends Action>> status,
      final String filename
  ) {
    try {
      final Graph graph = status.isSafe()
          ? ArgVisualizer.getDefault().visualize(status.asSafe().getProof())
          : TraceVisualizer.getDefault().visualize(status.asUnsafe().getCex());
      GraphvizWriter.getInstance().writeFile(graph, filename);
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    }
  }
}
