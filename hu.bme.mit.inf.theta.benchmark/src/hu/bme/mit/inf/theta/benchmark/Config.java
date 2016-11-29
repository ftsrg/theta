package hu.bme.mit.inf.theta.benchmark;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Timer;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.benchmark.Benchmark.MeasureResult;
import hu.bme.mit.inf.theta.benchmark.BenchmarkConfiguration.OptConfig;
import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker.CheckResult;
import hu.bme.mit.inf.theta.code.Parser;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.common.logging.impl.FileLogger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.utils.impl.CfaPrinter;
import hu.bme.mit.inf.theta.frontend.Optimizer;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.transform.ContextTransformer;
import hu.bme.mit.inf.theta.frontend.transform.FunctionTransformer;
import hu.bme.mit.inf.theta.solver.SolverManager;
import hu.bme.mit.inf.theta.solver.z3.Z3SolverManager;

public class Config {

	private String name;
	private Path testPath;
	private OptConfig optConfig = new OptConfig();
	private int timeout = 0;
	private boolean slice;
	private int maxBmcDepth = 20;
	private int logLevel = 7;
	private boolean isLBE = false;
	private boolean runnable = true;

	/// Timers
	private final Timer suiteTimer = new Timer();

	public Config(String name, Path testPath, int timeout) {
		this.name = name;
		this.testPath = testPath;
		this.timeout = timeout;
	}

	public Config(String name, String testPath, int timeout) {
		this(name, Paths.get(testPath), timeout);
	}

	public void addFunctionTransformer(FunctionTransformer pass) {
		this.optConfig.funcTransformers.add(pass);
	}

	public void addContextTransformer(ContextTransformer pass) {
		this.optConfig.contextTransformers.add(pass);
	}

	public void addPostContextFunctionTransformer(FunctionTransformer pass) {
		this.optConfig.postContextFunctionTransformers.add(pass);
	}

	public void setMaxBmcDepth(int depth) {
		this.maxBmcDepth = depth;
	}

	public void setSlice(boolean slice) {
		this.slice = slice;
	}

	public void setIsLBE(boolean isLBE) {
		this.isLBE = isLBE;
	}

	public void setLogLevel(int level) {
		this.logLevel = level;
	}

	public void setRunnable(boolean runnable) {
		this.runnable = runnable;
	}

	public List<MeasureResult> run() {
		List<MeasureResult> results = new ArrayList<>();

		System.out.println("========== " + "MEASURE" + " ==========");
		System.out.println("========== " + this.name + " ==========");
		try {
			List<String> tests = Files.walk(this.testPath)
					.filter(Files::isRegularFile)
					.filter(p -> p.toString().endsWith(".c"))
					.map(p -> p.toString())
					.collect(Collectors.toList());

			String logDirName = "logs/measure/" + this.name;

			for (String test : tests) {
				String logFileName = logDirName + test.replace('/', '_') + ".log";
				File logFile = new File(logFileName);

				if (!logFile.exists() && !logFile.isDirectory())
					logFile.createNewFile();

				Logger log = new FileLogger(this.logLevel, logFileName, true);

				System.out.print("MEASURE " + test + "...");
				List<MeasureResult> r = this.runBenchmark(test, log);

				results.addAll(r);
				System.out.println("\tDONE");
			}
		} catch (IOException e) {
			e.printStackTrace();
		}

		return results;
	}

	private List<MeasureResult> runBenchmark(String file, Logger log) {
		List<MeasureResult> results = new ArrayList<>();
		List<CFA> slices = this.compile(file, log, slice);

		for (int i = 0; i < slices.size(); i++) {
			CFA slice = slices.get(i);
			//System.out.println(CfaPrinter.toGraphvizSting(slice));

			SolverManager sm = new Z3SolverManager();

			Benchmark benchmark = new Benchmark(file, "test", 2000, 10, sm, 100, log);
			MeasureResult res = benchmark.run(slice, i);

			results.add(res);
		}

		return results;
	}

	private List<CFA> compile(String file, Logger log, boolean slice) {
		GlobalContext context = Parser.parse(file);
		Optimizer opt = optConfig.createOpt(context, log);

		opt.inlineGlobalVariables();
		opt.transform();

		opt.dump();

		List<CFA> cfas = slice ? opt.createCfaSlices(this.isLBE) : opt.createCfas();
		return cfas;
	}

	protected static class OptConfig {
		public List<FunctionTransformer> funcTransformers = new ArrayList<>();
		public List<ContextTransformer> contextTransformers = new ArrayList<>();
		public List<FunctionTransformer> postContextFunctionTransformers = new ArrayList<>();

		public Optimizer createOpt(GlobalContext context, Logger log) {
			Optimizer opt = new Optimizer(context);
			opt.setLogger(log);

			this.funcTransformers.forEach(t -> opt.addFunctionTransformer(t));
			this.contextTransformers.forEach(t -> opt.addContextTransformer(t));
			this.postContextFunctionTransformers.forEach(t -> opt.addPostContextFunctionTransformer(t));

			return opt;
		}

	}
}
