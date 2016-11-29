package hu.bme.mit.inf.theta.benchmark;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.theta.benchmark.Benchmark.MeasureResult;
import hu.bme.mit.inf.theta.benchmark.bmc.ErrorSearch;
import hu.bme.mit.inf.theta.code.Parser;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.inf.theta.common.logging.impl.FileLogger;
import hu.bme.mit.inf.theta.common.logging.impl.NullLogger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.utils.impl.CfaPrinter;
import hu.bme.mit.inf.theta.frontend.Optimizer;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.transform.ConstantPropagator;
import hu.bme.mit.inf.theta.frontend.transform.DeadBranchEliminator;
import hu.bme.mit.inf.theta.frontend.transform.FunctionInliner;
import hu.bme.mit.inf.theta.solver.SolverManager;
import hu.bme.mit.inf.theta.solver.z3.Z3SolverManager;

public class Application {

	private static List<Config> getConfigs(int timeout, int loglevel) {
		List<Config> configs = new ArrayList<>();

		Config trivialOpt0 = new Config("trivial_opt0", "benchmarks/trivial", timeout);
		trivialOpt0.setMaxBmcDepth(100);
		trivialOpt0.setSlice(false);
		trivialOpt0.setLogLevel(loglevel);
		//configs.add(trivialOpt0);

		Config trivialOpt1 = new Config("trivial_opt1", "benchmarks/trivial", timeout);
		trivialOpt1.setMaxBmcDepth(100);
		trivialOpt1.setLogLevel(loglevel);
		trivialOpt1.addFunctionTransformer(new ConstantPropagator());
		trivialOpt1.addFunctionTransformer(new DeadBranchEliminator());
		trivialOpt1.setSlice(true);
		configs.add(trivialOpt1);

		Config trivialOpt2 = new Config("trivial_opt2", "benchmarks/trivial", timeout);
		trivialOpt2.setMaxBmcDepth(100);
		trivialOpt2.addFunctionTransformer(new ConstantPropagator());
		trivialOpt2.addFunctionTransformer(new DeadBranchEliminator());
		trivialOpt2.addContextTransformer(new FunctionInliner());
		trivialOpt2.setSlice(true);
		configs.add(trivialOpt2);


		Config locksOpt0 = new Config("locks_opt0", "benchmarks/locks", timeout);
		locksOpt0.setMaxBmcDepth(100);
		locksOpt0.setSlice(false);
		locksOpt0.setLogLevel(loglevel);
		Config locksOpt1 = new Config("locks_opt1", "benchmarks/locks", timeout);
		locksOpt1.setMaxBmcDepth(100);
		locksOpt1.setLogLevel(loglevel);
		locksOpt1.setSlice(true);
		configs.add(locksOpt1);

		configs.add(locksOpt0);

		Config locksOpt2 = new Config("locks_opt2", "benchmarks/locks", timeout);
		locksOpt2.setMaxBmcDepth(100);
		locksOpt2.setLogLevel(loglevel);
		locksOpt2.setSlice(true);
		locksOpt2.addFunctionTransformer(new ConstantPropagator());
		locksOpt2.addFunctionTransformer(new DeadBranchEliminator());
		//configs.add(locksOpt2);

		Config ecaOpt0 = new Config("eca_opt0", "benchmarks/eca", timeout);
		ecaOpt0.addContextTransformer(new FunctionInliner());
		ecaOpt0.setMaxBmcDepth(200);
		ecaOpt0.setLogLevel(loglevel);
		ecaOpt0.setSlice(false);
		ecaOpt0.setRunnable(false);
		//configs.add(ecaOpt0);

		Config ecaOpt1 = new Config("eca_opt1", "benchmarks/eca", timeout);
		ecaOpt1.addContextTransformer(new FunctionInliner());
		ecaOpt1.setMaxBmcDepth(200);
		ecaOpt1.setLogLevel(7);
		ecaOpt1.setSlice(true);
		ecaOpt1.setRunnable(false);
		//configs.add(ecaOpt1);

		Config ecaOpt2 = new Config("eca_opt2", "benchmarks/eca", timeout);
		ecaOpt2.addFunctionTransformer(new ConstantPropagator());
		ecaOpt2.addFunctionTransformer(new DeadBranchEliminator());
		ecaOpt2.addContextTransformer(new FunctionInliner());
		ecaOpt2.addPostContextFunctionTransformer(new ConstantPropagator());
		ecaOpt2.addPostContextFunctionTransformer(new DeadBranchEliminator());
		ecaOpt2.setMaxBmcDepth(200);
		ecaOpt2.setLogLevel(loglevel);
		ecaOpt2.setSlice(true);
		ecaOpt2.setRunnable(false);
		//configs.add(ecaOpt2);

		return configs;

	}


	public static void main(String args[]) throws FileNotFoundException {/*
		List<MeasureResult> results = new ArrayList<>();

		String file = "benchmarks/locks/locks10_true.c";
		GlobalContext context = Parser.parse(file);

		Optimizer opt = new Optimizer(context);
		opt.setLogger(new NullLogger());

		opt.inlineGlobalVariables();
		opt.addFunctionTransformer(new ConstantPropagator());
		opt.addFunctionTransformer(new DeadBranchEliminator());
		opt.addContextTransformer(new FunctionInliner());
		opt.addPostContextFunctionTransformer(new ConstantPropagator());
		opt.addPostContextFunctionTransformer(new DeadBranchEliminator());
		opt.transform();

		List<CFA> slices = opt.getProgramSlices();

		for (int i = 0; i < slices.size(); i++) {
			CFA slice = slices.get(i);
			System.out.println(CfaPrinter.toGraphvizSting(slice));

			SolverManager sm = new Z3SolverManager();
			Logger log = new FileLogger(10, "/tmp/check.log", true);

			Benchmark benchmark = new Benchmark(file, "test", 2000, 10, sm, 100, log);
			MeasureResult res = benchmark.run(slice, i);

			results.add(res);
		}*/

		int timeout = 10000;
		List<Config> configs = getConfigs(timeout, 2);

		List<MeasureResult> results = new ArrayList<>();
		configs.forEach(config -> {
			results.addAll(config.run());
		});

		StringBuilder sb = new StringBuilder();
		sb.append("Test suite;File;Model ID;Locs;Edges;Depth;Status;Runtime;\n");
		for (MeasureResult result : results) {
			sb.append(String.format("%s;%s;%d;%d;%d;%d;%s;%d;\n",
				result.set,
				result.filename.substring(10),
				result.id,
				result.locCount,
				result.edgeCount,
				result.depth,
				result.check.toString(),
				result.runtime
			));
		}

		System.out.println(sb.toString());
	}


}

/*
package hu.bme.mit.inf.theta.benchmark;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.theta.benchmark.Config.MeasureResult;
import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker;
import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker.CheckResult;
import hu.bme.mit.inf.theta.code.Parser;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.utils.impl.CfaPrinter;
import hu.bme.mit.inf.theta.frontend.Optimizer;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.transform.ConstantPropagator;
import hu.bme.mit.inf.theta.frontend.transform.DeadBranchEliminator;
import hu.bme.mit.inf.theta.frontend.transform.FunctionInliner;
import hu.bme.mit.inf.theta.frontend.transform.LoopUnroller;

public class Application {

	public static List<Config> getConfigs(int timeout, int loglevel) {
		List<Config> configs = new ArrayList<>();

		Config trivialOpt0 = new Config("trivial_opt0", "benchmarks/trivial", timeout);
		trivialOpt0.setMaxBmcDepth(100);
		trivialOpt0.setSlice(false);
		trivialOpt0.setLogLevel(loglevel);
		//configs.add(trivialOpt0);

		Config trivialOpt1 = new Config("trivial_opt1", "benchmarks/trivial", timeout);
		trivialOpt1.setMaxBmcDepth(100);
		trivialOpt1.setLogLevel(loglevel);
		trivialOpt1.addFunctionTransformer(new ConstantPropagator());
		trivialOpt1.addFunctionTransformer(new DeadBranchEliminator());
		trivialOpt1.setSlice(true);
		configs.add(trivialOpt1);

		Config trivialOpt2 = new Config("trivial_opt2", "benchmarks/trivial", timeout);
		trivialOpt2.setMaxBmcDepth(100);
		trivialOpt2.addFunctionTransformer(new ConstantPropagator());
		trivialOpt2.addFunctionTransformer(new DeadBranchEliminator());
		trivialOpt2.addContextTransformer(new FunctionInliner());
		trivialOpt2.setSlice(true);
		configs.add(trivialOpt2);


		Config locksOpt0 = new Config("locks_opt0", "benchmarks/locks", timeout);
		locksOpt0.setMaxBmcDepth(100);
		locksOpt0.setSlice(false);
		locksOpt0.setLogLevel(loglevel);
		Config locksOpt1 = new Config("locks_opt1", "benchmarks/locks", timeout);
		locksOpt1.setMaxBmcDepth(100);
		locksOpt1.setLogLevel(loglevel);
		locksOpt1.setSlice(true);
		configs.add(locksOpt1);

		configs.add(locksOpt0);

		Config locksOpt2 = new Config("locks_opt2", "benchmarks/locks", timeout);
		locksOpt2.setMaxBmcDepth(100);
		locksOpt2.setLogLevel(loglevel);
		locksOpt2.setSlice(true);
		locksOpt2.addFunctionTransformer(new ConstantPropagator());
		locksOpt2.addFunctionTransformer(new DeadBranchEliminator());
		//configs.add(locksOpt2);

		Config ecaOpt0 = new Config("eca_opt0", "benchmarks/eca", timeout);
		ecaOpt0.addContextTransformer(new FunctionInliner());
		ecaOpt0.setMaxBmcDepth(200);
		ecaOpt0.setLogLevel(loglevel);
		ecaOpt0.setSlice(false);
		//ecaOpt0.setRunnable(false);
		configs.add(ecaOpt0);

		Config ecaOpt1 = new Config("eca_opt1", "benchmarks/eca", timeout);
		ecaOpt1.addContextTransformer(new FunctionInliner());
		ecaOpt1.setMaxBmcDepth(200);
		ecaOpt1.setLogLevel(7);
		ecaOpt1.setSlice(true);
		//ecaOpt1.setRunnable(false);
		configs.add(ecaOpt1);

		Config ecaOpt2 = new Config("eca_opt2", "benchmarks/eca", timeout);
		ecaOpt2.addFunctionTransformer(new ConstantPropagator());
		ecaOpt2.addFunctionTransformer(new DeadBranchEliminator());
		ecaOpt2.addContextTransformer(new FunctionInliner());
		ecaOpt2.addPostContextFunctionTransformer(new ConstantPropagator());
		ecaOpt2.addPostContextFunctionTransformer(new DeadBranchEliminator());
		ecaOpt2.setMaxBmcDepth(200);
		ecaOpt2.setLogLevel(loglevel);
		ecaOpt2.setSlice(true);
		//ecaOpt2.setRunnable(false);
		configs.add(ecaOpt2);

		return configs;
	}

	public static void main(String[] args) throws IOException {
		System.in.read();
		int timeout = 1000;

		List<Config> configs = getConfigs(timeout, 7);

		List<MeasureResult> results = new ArrayList<>();
		configs.forEach(config -> {
			results.addAll(config.measure());
		});


		StringBuilder sb = new StringBuilder();
		sb.append("Test suite;File;Model ID;Locs;Edges;Depth;Status;Runtime;\n");
		for (MeasureResult result : results) {
			sb.append(String.format("%s;%s;%d;%d;%d;%d;%s;%d;\n",
				result.set,
				result.filename.substring(10),
				result.id,
				result.locCount,
				result.edgeCount,
				result.depth,
				result.check.toString(),
				result.runtime
			));
		}

		System.out.println(sb.toString());



		configs.forEach(config -> {
			//config.run();
		});

		// FIXME: I don't know why is this needed, but otherwise a thread would do an infinite loop
		System.exit(0);
	}
}
*/