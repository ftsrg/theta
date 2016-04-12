package hu.bme.mit.inf.ttmc.cegar.tests.performance;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Date;
import java.util.List;
import java.util.Locale;

import org.junit.Assert;

import hu.bme.mit.inf.ttmc.aiger.impl.AIGERLoaderOptimized;
import hu.bme.mit.inf.ttmc.aiger.impl.AIGERLoaderSimple;
import hu.bme.mit.inf.ttmc.cegar.common.CEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.CEGARLoop;
import hu.bme.mit.inf.ttmc.cegar.common.CEGARResult;
import hu.bme.mit.inf.ttmc.cegar.tests.formatters.Formatter;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;
import hu.bme.mit.inf.ttmc.solver.z3.Z3ConstraintManager;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelCreator;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelLoader;

public class PerfTestBase {

	private STSManager createNewManager() {
		return new STSManagerImpl(new Z3ConstraintManager());
	}

	protected void run(final List<TestCase> testCases, final List<CEGARBuilder> configurations, final int timeOut, final Formatter formatter) {
		boolean allOk = true;

		final TestResult[][] results = new TestResult[testCases.size()][configurations.size()];

		System.out.println("Running " + testCases.size() + " test cases with " + configurations.size() + " configurations");
		System.out.println("Started at " + new Date());

		// Header
		formatter.cell("");
		for (final CEGARBuilder cegar : configurations)
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

		for (int i = 0; i < testCases.size(); i++) {
			final TestCase testCase = testCases.get(i);
			formatter.cell((testCase.expected ? "(+) " : "(-) ") + testCase.path.substring(testCase.path.lastIndexOf('/') + 1));

			for (int j = 0; j < configurations.size(); j++) {
				final CEGARBuilder configuration = configurations.get(j);
				results[i][j] = run(testCase, configuration, timeOut);
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
		System.out.println("Done at " + new Date());
		Assert.assertTrue(allOk);
	}

	protected TestResult run(final TestCase testCase, final CEGARBuilder configuration, final int timeOut) {
		STS system;
		try {
			system = testCase.loader.load(testCase.path, createNewManager());
		} catch (final IOException e1) {
			return new TestResult(TestResult.ResultType.IOException, new ArrayList<>());
		}
		CEGARLoop cegar = configuration.build();
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
							system = testCase.loader.load(testCase.path, createNewManager());
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
		public final CEGARLoop cegar;
		public final STS system;
		public volatile CEGARResult result;

		public CEGARRunner(final CEGARLoop cegar, final STS system) {
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
