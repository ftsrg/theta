package hu.bme.mit.inf.theta.benchmark;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Timer;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.stream.Collectors;

import com.google.common.base.Stopwatch;

import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker;
import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker.CheckResult;
import hu.bme.mit.inf.theta.benchmark.utils.CfaMeasures;
import hu.bme.mit.inf.theta.code.Parser;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.common.logging.impl.FileLogger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.utils.impl.CfaPrinter;
import hu.bme.mit.inf.theta.frontend.Optimizer;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.transform.ConstantPropagator;
import hu.bme.mit.inf.theta.frontend.transform.ContextTransformer;
import hu.bme.mit.inf.theta.frontend.transform.DeadBranchEliminator;
import hu.bme.mit.inf.theta.frontend.transform.FunctionTransformer;

public class BenchmarkConfiguration {


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

	public BenchmarkConfiguration(String name, Path testPath, int timeout) {
		this.name = name;
		this.testPath = testPath;
		this.timeout = timeout;
	}

	public BenchmarkConfiguration(String name, String testPath, int timeout) {
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

	public void run() {
		System.out.println("========== " + this.name + " ==========");
		try {
			List<String> tests = Files.walk(this.testPath)
					.filter(Files::isRegularFile)
					.filter(p -> p.toString().endsWith(".c"))
					.map(p -> p.toString())
					.collect(Collectors.toList());

			String logDirName = "logs/" + this.name;

			for (String test : tests) {
				String logFileName = logDirName + test.replace('/', '_') + ".log";
				File logFile = new File(logFileName);

				if (!logFile.exists() && !logFile.isDirectory())
					logFile.createNewFile();

				Logger log = new FileLogger(this.logLevel, logFileName, true);

				System.out.print("TEST " + test + "...");

				try {
					CheckResult res = this.runBenchmark(test, log, this.slice);
					switch (res) {
					case CHECK_FAILED:
						System.out.println("\t FAILED");
						break;
					case CHECK_PASSED:
						System.out.println("\t PASSED");
						break;
					case CHECK_UNKNOWN:
						System.out.println("\t UNKNOWN");
						break;
					case CHECK_TIMEOUT:
						System.out.println("\t TIMEOUT");
						break;
					case CHECK_INTERNAL_ERROR:
						System.out.println("\t INTERNAL_ERROR");
						break;
					}
				} catch (Exception ex) {
					System.out.println("    EXCEPTION: " + ex.getMessage());
					ex.printStackTrace();
					log.writeln(ex, 0);
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}

	}

	public List<MeasureResult> measure() {
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
				List<MeasureResult> r = this.benchmark(test, log, slice);

				results.addAll(r);
				System.out.println("\tDONE");
			}
		} catch (IOException e) {
			e.printStackTrace();
		}

		return results;
	}

	protected List<MeasureResult> benchmark(String file, Logger log, boolean slice) {
		List<MeasureResult> results = new ArrayList<>();
		List<CFA> cfas = this.compile(file, log, slice);

		if (cfas.size() == 0) // if no slices were found for asserts, then no asserts can fail
			throw new AssertionError("There should be at least one slice");

		int count = 0;
		BoundedModelChecker bmc = new BoundedModelChecker(log);

		for (CFA cfa : cfas) {
			log.writeHeader("CFA SLICE", 1);
			log.writeln(CfaPrinter.toGraphvizSting(cfa), 1);
			MeasureResult res = new MeasureResult(cfa, file, count++, this.name);

			if (this.runnable) {
				ExecutorService exec = Executors.newSingleThreadExecutor();
				BmcRunner runner = new BmcRunner(bmc, this.maxBmcDepth, cfa);
				Future<CheckResult> future = exec.submit(runner);

				Stopwatch sw = Stopwatch.createUnstarted();

				try {
					sw.start();
					CheckResult check = future.get(this.timeout, TimeUnit.MILLISECONDS);
					sw.stop();

					res.check = check;
					res.runtime = sw.elapsed(TimeUnit.MILLISECONDS);
				} catch (TimeoutException ex) {
					future.cancel(true);
					sw.stop();
					res.check = CheckResult.CHECK_TIMEOUT;
					res.runtime = sw.elapsed(TimeUnit.MILLISECONDS);
				} catch (Exception ex) {
					ex.printStackTrace();
					throw new AssertionError("Don't do this please");
				} finally {
					future.cancel(true);
					exec.shutdown();
					sw.reset();
				}

			}

			results.add(res);
		}

		return results;
	}

	protected CheckResult runBenchmark(String file, Logger log, boolean slice) {
		List<CFA> cfas = this.compile(file, log, slice);

		if (cfas.size() == 0) // if no slices were found for asserts, then no asserts can fail
			return CheckResult.CHECK_PASSED;

		cfas.forEach(cfa -> {
			log.writeHeader("CFA SLICES", 1);
			log.writeln(CfaPrinter.toGraphvizSting(cfa), 1);
		});

		BoundedModelChecker bmc = new BoundedModelChecker(log);

		for (CFA cfa : cfas) {
			ExecutorService exec = Executors.newSingleThreadExecutor();
			BmcRunner runner = new BmcRunner(bmc, this.maxBmcDepth, cfa);

			Future<CheckResult> future = exec.submit(runner);

			try {
				CheckResult res = future.get(this.timeout, TimeUnit.MILLISECONDS);

				if (res == CheckResult.CHECK_FAILED)
					return CheckResult.CHECK_FAILED;
				else if (res == CheckResult.CHECK_INTERNAL_ERROR)
					return CheckResult.CHECK_INTERNAL_ERROR;

			} catch (TimeoutException ex) {
				future.cancel(true);
				return CheckResult.CHECK_TIMEOUT;
			} catch (Exception ex) {
				ex.printStackTrace();
				return CheckResult.CHECK_INTERNAL_ERROR;
			} finally {
				future.cancel(true);
				exec.shutdown();
			}
		}

		return CheckResult.CHECK_UNKNOWN;
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

	protected static class BmcRunner implements Callable<CheckResult> {

		public volatile CheckResult res = CheckResult.CHECK_INTERNAL_ERROR;
		public BoundedModelChecker bmc;
		public int k;
		public CFA cfa;

		public BmcRunner(BoundedModelChecker bmc, int k, CFA cfa) {
			this.bmc = bmc;
			this.k = k;
			this.cfa = cfa;
		}

		@Override
		public CheckResult call() {
			return this.bmc.check(this.cfa, this.k);
		}

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

	public static class MeasureResult {
		public static int count = 0;
		public int id;
		public CFA cfa;
		public String filename;
		public String set;

		public int locCount;
		public int depth;
		public int edgeCount;
		public CheckResult check = CheckResult.CHECK_TIMEOUT;
		public long runtime = -1;

		public MeasureResult(CFA cfa, String filename, int id, String set) {
			this.cfa = cfa;
			this.filename = filename;
			this.id = id;
			this.set = set;

			this.locCount = cfa.getLocs().size();
			this.edgeCount = cfa.getEdges().size();
			this.depth = CfaMeasures.depth(cfa);
		}
	}



}
