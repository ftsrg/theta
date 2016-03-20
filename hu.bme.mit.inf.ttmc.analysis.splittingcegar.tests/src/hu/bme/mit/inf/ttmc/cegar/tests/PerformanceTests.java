package hu.bme.mit.inf.ttmc.cegar.tests;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.aiger.impl.AIGERLoaderOptimized;
import hu.bme.mit.inf.ttmc.cegar.common.CEGARResult;
import hu.bme.mit.inf.ttmc.cegar.common.ICEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.ICEGARLoop;
import hu.bme.mit.inf.ttmc.constraint.z3.Z3ConstraintManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelCreator;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelLoader;

public class PerformanceTests {
	private final STSManager manager = new STSManagerImpl(new Z3ConstraintManager());

	private TestResult run(final TestCase testCase, final ICEGARBuilder configuration, final int timeOut) throws IOException {
		final STS system = loadModel(testCase.path);
		final ICEGARLoop cegar = configuration.build();
		final CEGARRunner runner = new CEGARRunner(cegar, system);

		runner.start();
		try {
			runner.join(timeOut);
			cegar.stop();
			runner.join();
			if (runner.result == null) {
				return new TestResult(TestResult.ResultType.Timeout, new ArrayList<>());
			} else {
				final List<CEGARResult> resultList = new ArrayList<>();
				resultList.add(runner.result);
				if (runner.result.specificationHolds() != testCase.expected) {
					return new TestResult(TestResult.ResultType.False, resultList);
				} else {
					// TODO run more tests if runtime is short
					return new TestResult(TestResult.ResultType.Ok, resultList);
				}
			}
		} catch (final InterruptedException e) {
			System.out.println("Interrupted exception in" + cegar + " for model " + testCase.path + ".");
		}

		return null;
	}

	private STS loadModel(final String path) throws IOException {
		if (path.endsWith(".system")) {
			// It is assumed that the file contains _exactly one_ STS
			return SystemModelCreator.create(manager, SystemModelLoader.getInstance().load(path)).getSTSs().iterator().next();
		} else if (path.endsWith(".aag")) {
			return new AIGERLoaderOptimized().load(path, manager);
		} else {
			throw new UnsupportedOperationException("Cannot determine model type by extension.");
		}
	}

	private static class TestResult {
		public enum ResultType {
			Ok, False, Timeout
		};

		public ResultType resultType;
		public List<CEGARResult> results;

		public TestResult(final ResultType resultType, final Collection<CEGARResult> results) {
			this.resultType = resultType;
			this.results = new ArrayList<>(results);
		}
	}

	private static class TestCase {
		public String path;
		public boolean expected;

		public TestCase(final String path, final boolean expected) {
			this.path = path;
			this.expected = expected;
		}
	}

	private static class CEGARRunner extends Thread {
		public final ICEGARLoop cegar;
		public final STS system;
		public volatile CEGARResult result;

		public CEGARRunner(final ICEGARLoop cegar, final STS system) {
			this.cegar = cegar;
			this.system = system;
			this.result = null;
		}

		@Override
		public void run() {
			result = cegar.check(system);
		}
	}
}
