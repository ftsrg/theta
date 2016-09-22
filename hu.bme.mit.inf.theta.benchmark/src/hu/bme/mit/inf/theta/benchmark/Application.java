package hu.bme.mit.inf.theta.benchmark;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker;
import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker.CheckResult;
import hu.bme.mit.inf.theta.code.Parser;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.common.logging.impl.FileLogger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.utils.impl.CfaPrinter;
import hu.bme.mit.inf.theta.frontend.Optimizer;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.transform.ConstantPropagator;
import hu.bme.mit.inf.theta.frontend.transform.DeadBranchEliminator;
import hu.bme.mit.inf.theta.frontend.transform.DeadInstructionElimination;

public class Application {

	public static void main(String[] args) {
		Path path = Paths.get("benchmarks");

		try {
			List<String> tests = Files.walk(path)
				.filter(Files::isRegularFile)
				.filter(p -> p.toString().endsWith(".c"))
				.map(p -> p.toString())
				.collect(Collectors.toList());

			for (String test : tests) {
				String logFileName = "logs/" + test.replace('/', '_') + ".log";
				File logFile = new File(logFileName);

				if (!logFile.exists() && !logFile.isDirectory())
					logFile.createNewFile();

				Logger log = new FileLogger(6, logFileName, true);

				System.out.print("TEST " + test + "...");

				try {
					CheckResult res = runBenchmark(test, log);
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
					default:
						break;
					}

				} catch (Exception ex) {
					System.out.println("    EXCEPTION: " + ex.getMessage());
					log.writeln(ex, 0);
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static CheckResult runBenchmark(String file, Logger log) {
		GlobalContext context = Parser.parse(file);
		Optimizer opt = new Optimizer(context);
		opt.setLogger(log);

		opt.addFunctionTransformer(new ConstantPropagator());
		opt.addFunctionTransformer(new DeadBranchEliminator());

		opt.transform();

		opt.dump();

		List<CFA> cfas = opt.createCfaSlices();
		cfas.forEach(cfa -> {
			log.writeHeader("CFA SLICES", 1);
			log.writeln(CfaPrinter.toGraphvizSting(cfa), 1);
		});

		BoundedModelChecker bmc = new BoundedModelChecker(log);
		CheckResult res = bmc.checkAll(opt.createCfaSlices(), 40);

		return res;
	}


}
