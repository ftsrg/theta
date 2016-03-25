package hu.bme.mit.inf.ttmc.cegar.tests.performance;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Locale;

import org.junit.Assert;

import hu.bme.mit.inf.ttmc.aiger.impl.AIGERLoaderOptimized;
import hu.bme.mit.inf.ttmc.aiger.impl.AIGERLoaderSimple;
import hu.bme.mit.inf.ttmc.cegar.common.CEGARResult;
import hu.bme.mit.inf.ttmc.cegar.common.ICEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.ICEGARLoop;
import hu.bme.mit.inf.ttmc.cegar.tests.formatters.IFormatter;
import hu.bme.mit.inf.ttmc.constraint.z3.Z3ConstraintManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelCreator;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelLoader;

public class PerfTestBase {
	protected void run(final List<TestCase> testCases, final List<ICEGARBuilder> configurations, final int timeOut, final IFormatter formatter) {
		boolean allOk = true;

		final TestResult[][] results = new TestResult[testCases.size()][configurations.size()];

		for (int i = 0; i < testCases.size(); i++) {
			final TestCase testCase = testCases.get(i);
			System.out.println("Running model " + (i + 1) + "/" + testCases.size() + " [" + testCase.path + "]");
			for (int j = 0; j < configurations.size(); j++) {
				final ICEGARBuilder configuration = configurations.get(j);
				System.out.println("\tConfiguration " + (j + 1) + "/" + configurations.size() + " [" + configuration.build() + "]");
				results[i][j] = run(testCase, configuration, timeOut);
			}
		}

		System.out.println("-------------------------");
		System.out.println("RESULTS");
		System.out.println("-------------------------");

		// Header
		formatter.cell("");
		for (final ICEGARBuilder cegar : configurations)
			formatter.cell(cegar.build() + "", 4);
		formatter.newRow();
		formatter.cell("");
		for (int i = 0; i < configurations.size(); ++i) {
			formatter.cell("#");
			formatter.cell("T");
			formatter.cell("#R");
			formatter.cell("#S");
		}
		formatter.newRow();
		// Body
		for (int i = 0; i < testCases.size(); i++) {
			formatter.cell((testCases.get(i).expected ? "(+) " : "(-) ") + testCases.get(i).path.substring(testCases.get(i).path.lastIndexOf('/') + 1));
			for (int j = 0; j < configurations.size(); j++) {
				final TestResult result = results[i][j];
				if (result.resultType == TestResult.ResultType.Ok) {
					formatter.cell(result.results.size() + "");
					formatter.cell(String.format(Locale.ENGLISH, "%.0f", result.getAvgTime()));
					formatter.cell(result.results.get(0).getRefinementCount() + "");
					formatter.cell(result.results.get(0).getStateSpaceSize() + "");
				} else {
					formatter.cell(result.resultType.toString(), 4);
					if (result.resultType != TestResult.ResultType.Timeout)
						allOk = false;
				}
			}
			formatter.newRow();
		}

		Assert.assertTrue(allOk);
	}

	protected TestResult run(final TestCase testCase, final ICEGARBuilder configuration, final int timeOut) {
		STS system;
		try {
			system = testCase.loader.load(testCase.path, new STSManagerImpl(new Z3ConstraintManager()));
		} catch (final IOException e1) {
			return new TestResult(TestResult.ResultType.IOException, new ArrayList<>());
		}
		ICEGARLoop cegar = configuration.build();
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
				if (runner.result.propertyHolds() != testCase.expected) {
					return new TestResult(TestResult.ResultType.False, resultList);
				} else {
					int rerun = 0;
					if (runner.result.getElapsedMillis() < 1000)
						rerun = 4;
					else if (runner.result.getElapsedMillis() < 5000)
						rerun = 2;
					else if (runner.result.getElapsedMillis() < 10000)
						rerun = 1;
					for (int i = 0; i < rerun; ++i) {
						try {
							system = testCase.loader.load(testCase.path, new STSManagerImpl(new Z3ConstraintManager()));
						} catch (final IOException e1) {
							return new TestResult(TestResult.ResultType.IOException, new ArrayList<>());
						}
						cegar = configuration.build();
						resultList.add(cegar.check(system));
					}
					return new TestResult(TestResult.ResultType.Ok, resultList);
				}
			}
		} catch (final InterruptedException e) {
			System.out.println("Interrupted exception in" + cegar + " for model " + testCase.path + ".");
		}

		return null;
	}

	protected static interface IModelLoader {
		STS load(final String path, final STSManager manager) throws IOException;
	}

	protected static class SystemFileModelLoader implements IModelLoader {
		@Override
		public STS load(final String path, final STSManager manager) {
			return SystemModelCreator.create(manager, SystemModelLoader.getInstance().load(path)).getSTSs().iterator().next();
		}
	}

	protected static class AIGERFileModelLoaderOptimized implements IModelLoader {

		@Override
		public STS load(final String path, final STSManager manager) throws IOException {
			return new AIGERLoaderOptimized().load(path, manager);
		}
	}

	protected static class AIGERFileModelLoaderSimple implements IModelLoader {

		@Override
		public STS load(final String path, final STSManager manager) throws IOException {
			return new AIGERLoaderSimple().load(path, manager);
		}
	}

	protected static class TestResult {
		public enum ResultType {
			Ok, False, Timeout, IOException
		};

		public ResultType resultType;
		public List<CEGARResult> results;

		public TestResult(final ResultType resultType, final Collection<CEGARResult> results) {
			this.resultType = resultType;
			this.results = new ArrayList<>(results);
		}

		public double getAvgTime() {
			return results.stream().mapToDouble(r -> r.getElapsedMillis()).average().getAsDouble();
		}
	}

	protected static class TestCase {
		public String path;
		public boolean expected;
		public IModelLoader loader;

		public TestCase(final String path, final boolean expected, final IModelLoader loader) {
			this.path = path;
			this.expected = expected;
			this.loader = loader;
		}
	}

	protected static class CEGARRunner extends Thread {
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
