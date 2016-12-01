package hu.bme.mit.theta.frontend.c.benchmark;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.TimeUnit;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.frontend.c.benchmark.bmc.ErrorSearch;
import hu.bme.mit.theta.frontend.c.benchmark.bmc.ErrorSearch.CheckResult;
import hu.bme.mit.theta.solver.SolverFactory;

public class Benchmark {

	private final String file;
	private final String set;
	private Stopwatch sw = Stopwatch.createUnstarted();
	private final int timeout;
	private final int runCount;
	private final SolverFactory factory;
	private final int maxBound;
	private final Logger log;

	public Benchmark(String file, String set, int timeout, int runCount, SolverFactory factory, int maxBound,
			Logger log) {
		this.file = file;
		this.set = set;
		this.timeout = timeout;
		this.runCount = runCount;
		this.factory = factory;
		this.maxBound = maxBound;
		this.log = log;
	}

	public MeasureResult run(CFA cfa, int num) {
		MeasureResult res = new MeasureResult(cfa, this.file, num, this.set);

		int i = 0;
		List<Long> times = new ArrayList<>();
		while (i < runCount) {
			this.log.writeln(">>> Starting benchmark " + i + "...", 2);
			this.sw.reset();
			this.sw.start();

			BmcRunner runner = new BmcRunner(cfa, this.maxBound, this.log, this.factory);
			Thread wt = new Thread(runner);

			try {
				wt.start();
				wt.join(this.timeout);
			} catch (InterruptedException e) {
			}

			this.sw.stop();

			res.check = runner.result;
			long elapsed = this.sw.elapsed(TimeUnit.MILLISECONDS);
			this.log.writeln(">>> Benchmark " + i + " finished, running time: " + elapsed + " ms", 2);
			i = i + 1;

			times.add(elapsed);
		}

		Collections.sort(times);
		// Remove the smallest and largest values
		times.remove(0);
		times.remove(times.size() - 1);

		double med = times.stream().mapToLong(a -> a).average().getAsDouble();

		res.runtime = Math.round(med);

		this.log.writeHeader("Avarage running time: " + med + " ms", 2);

		return res;
	}

	private static class BmcRunner implements Runnable {
		private final CFA cfa;
		private final ErrorSearch bmc;
		private final SolverFactory factory;
		private final int maxBound;
		private final Logger log;
		private CheckResult result = CheckResult.CHECK_TIMEOUT;

		public BmcRunner(CFA cfa, int maxBound, Logger log, SolverFactory factory) {
			// this.manager = new Z3SolverManager();
			this.cfa = cfa;
			this.maxBound = maxBound;
			this.log = log;
			this.factory = factory;
			this.bmc = new ErrorSearch(this.cfa, this.factory.createSolver(), this.log);
		}

		@Override
		public void run() {
			this.result = this.bmc.check(this.maxBound);
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
		}
	}

}
