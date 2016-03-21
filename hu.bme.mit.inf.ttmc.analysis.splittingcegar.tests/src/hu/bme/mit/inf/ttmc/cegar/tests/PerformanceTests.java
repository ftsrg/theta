package hu.bme.mit.inf.ttmc.cegar.tests;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Locale;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.aiger.impl.AIGERLoaderOptimized;
import hu.bme.mit.inf.ttmc.aiger.impl.AIGERLoaderSimple;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.ClusteredCEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.CEGARResult;
import hu.bme.mit.inf.ttmc.cegar.common.ICEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.ICEGARLoop;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.InterpolatingCEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.InterpolatingCEGARBuilder.InterpolationMethod;
import hu.bme.mit.inf.ttmc.cegar.tests.formatters.ExcelFormatter;
import hu.bme.mit.inf.ttmc.cegar.tests.formatters.IFormatter;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.VisibleCEGARBuilder;
import hu.bme.mit.inf.ttmc.constraint.z3.Z3ConstraintManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelCreator;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelLoader;

public class PerformanceTests {
	private STSManager manager = new STSManagerImpl(new Z3ConstraintManager());
	private final IFormatter formatter = new ExcelFormatter();

	@SuppressWarnings("serial")
	//@Test
	public void testSimple() {
		final IModelLoader loader = new SystemFileModelLoader();

		final List<TestCase> testCases = new ArrayList<TestCase>() {
			{
				add(new TestCase("models/simple/simple1.system", false, loader));
				add(new TestCase("models/simple/simple2.system", true, loader));
				add(new TestCase("models/simple/simple3.system", false, loader));
				add(new TestCase("models/simple/counter.system", true, loader));
				add(new TestCase("models/simple/counter_bad.system", false, loader));
				add(new TestCase("models/simple/counter_parametric.system", true, loader));
				add(new TestCase("models/simple/boolean1.system", false, loader));
				add(new TestCase("models/simple/boolean2.system", false, loader));
				add(new TestCase("models/simple/readerswriters.system", true, loader));
				add(new TestCase("models/simple/loop.system", true, loader));
				add(new TestCase("models/simple/loop_bad.system", false, loader));
			}
		};
		final List<ICEGARBuilder> configurations = new ArrayList<ICEGARBuilder>() {
			{
				add(new ClusteredCEGARBuilder().logger(null).visualizer(null).manager(manager));
				add(new VisibleCEGARBuilder().logger(null).visualizer(null).manager(manager).useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(false)
						.useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(true)
						.useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(true)
						.useCNFTransformation(true));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Sequence)
						.incrementalModelChecking(true).useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Sequence)
						.incrementalModelChecking(true).useCNFTransformation(true));
			}
		};

		run(testCases, configurations, 10000);
	}

	@SuppressWarnings("serial")
	//@Test
	public void testCERNPLC() {
		final IModelLoader loader = new SystemFileModelLoader();

		final List<TestCase> testCases = new ArrayList<TestCase>() {
			{
				add(new TestCase("models/cern/LOCAL_vc1.system", false, loader));
				add(new TestCase("models/cern/LOCAL_vc2.system", false, loader));
				add(new TestCase("models/cern/REQ_1-1.system", true, loader));
				add(new TestCase("models/cern/REQ_1-8_correct.system", true, loader));
				add(new TestCase("models/cern/REQ_1-8_incorrect.system", false, loader));
				add(new TestCase("models/cern/REQ_1-9.system", true, loader));
				add(new TestCase("models/cern/REQ_2-3b_correct.system", true, loader));
				add(new TestCase("models/cern/REQ_2-3b_incorrect.system", false, loader));
				add(new TestCase("models/cern/REQ_3-1.system", true, loader));
				add(new TestCase("models/cern/REQ_3-2.system", false, loader));
				add(new TestCase("models/cern/UCPC-1721.system", true, loader));
			}
		};
		final List<ICEGARBuilder> configurations = new ArrayList<ICEGARBuilder>() {
			{
				add(new VisibleCEGARBuilder().logger(null).visualizer(null).manager(manager).useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(true)
						.useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(true)
						.useCNFTransformation(false).explicitVariable("loc"));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Sequence)
						.incrementalModelChecking(true).useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Sequence)
						.incrementalModelChecking(true).useCNFTransformation(false).explicitVariable("loc"));
			}
		};

		run(testCases, configurations, 30 * 60 * 1000);
	}

	@SuppressWarnings("serial")
	//@Test
	public void testFischer() {
		final IModelLoader loader = new SystemFileModelLoader();

		final List<TestCase> testCases = new ArrayList<TestCase>() {
			{
				add(new TestCase("models/fischer/fischer2.system", true, loader));
				add(new TestCase("models/fischer/fischer2_bad.system", false, loader));
				add(new TestCase("models/fischer/fischer3_bool.system", true, loader));
				add(new TestCase("models/fischer/fischer3_bool_bad.system", false, loader));
			}
		};
		final List<ICEGARBuilder> configurations = new ArrayList<ICEGARBuilder>() {
			{
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(true)
						.useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Sequence)
						.incrementalModelChecking(true).useCNFTransformation(false));
			}
		};

		run(testCases, configurations, 5 * 60 * 1000);
	}

	@SuppressWarnings("serial")
	@Test
	public void testHardware() {
		final IModelLoader loader = new AIGERFileModelLoaderOptimized();
		//final IModelLoader loader = new AIGERFileModelLoaderSimple();

		final List<TestCase> testCases = new ArrayList<TestCase>() {
			{
				add(new TestCase("models/hardware/ringp0.aag", false, loader));
				add(new TestCase("models/hardware/ringp0neg.aag", false, loader));
				add(new TestCase("models/hardware/shortp0.aag", false, loader));
				add(new TestCase("models/hardware/shortp0neg.aag", false, loader));
				add(new TestCase("models/hardware/srg5ptimo.aag", false, loader));
				add(new TestCase("models/hardware/srg5ptimoneg.aag", false, loader));
				add(new TestCase("models/hardware/srg5ptimonegnv.aag", false, loader));
				add(new TestCase("models/hardware/nusmv.syncarb5_2.B.aag", true, loader));
				add(new TestCase("models/hardware/nusmv.syncarb10_2.B.aag", true, loader));
				add(new TestCase("models/hardware/mutexp0.aag", false, loader));
				add(new TestCase("models/hardware/mutexp0neg.aag", false, loader));
				add(new TestCase("models/hardware/pdtpmsarbiter.aag", true, loader));

			}
		};
		final List<ICEGARBuilder> configurations = new ArrayList<ICEGARBuilder>() {
			{
				//add(new VisibleCEGARBuilder().logger(null).visualizer(null).manager(manager).useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(true)
						.useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Sequence)
						.incrementalModelChecking(true).useCNFTransformation(false));
			}
		};

		run(testCases, configurations, 5 * 60 * 1000);
	}

	private void run(final List<TestCase> testCases, final List<ICEGARBuilder> configurations, final int timeOut) {
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

	private TestResult run(final TestCase testCase, final ICEGARBuilder configuration, final int timeOut) {
		manager = new STSManagerImpl(new Z3ConstraintManager());
		STS system;
		try {
			system = testCase.loader.load(testCase.path, manager);
		} catch (final IOException e1) {
			return new TestResult(TestResult.ResultType.IOException, new ArrayList<>());
		}
		ICEGARLoop cegar = configuration.manager(manager).build();
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
					int rerun = 0;
					if (runner.result.getElapsedMillis() < 1000)
						rerun = 4;
					else if (runner.result.getElapsedMillis() < 5000)
						rerun = 2;
					else if (runner.result.getElapsedMillis() < 10000)
						rerun = 1;
					for (int i = 0; i < rerun; ++i) {
						manager = new STSManagerImpl(new Z3ConstraintManager());
						try {
							system = testCase.loader.load(testCase.path, manager);
						} catch (final IOException e1) {
							return new TestResult(TestResult.ResultType.IOException, new ArrayList<>());
						}
						cegar = configuration.manager(manager).build();
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

	private static interface IModelLoader {
		STS load(final String path, final STSManager manager) throws IOException;
	}

	private static class SystemFileModelLoader implements IModelLoader {
		@Override
		public STS load(final String path, final STSManager manager) {
			return SystemModelCreator.create(manager, SystemModelLoader.getInstance().load(path)).getSTSs().iterator().next();
		}
	}

	private static class AIGERFileModelLoaderOptimized implements IModelLoader {

		@Override
		public STS load(final String path, final STSManager manager) throws IOException {
			return new AIGERLoaderOptimized().load(path, manager);
		}
	}

	private static class AIGERFileModelLoaderSimple implements IModelLoader {

		@Override
		public STS load(final String path, final STSManager manager) throws IOException {
			return new AIGERLoaderSimple().load(path, manager);
		}
	}

	private static class TestResult {
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

	private static class TestCase {
		public String path;
		public boolean expected;
		public IModelLoader loader;

		public TestCase(final String path, final boolean expected, final IModelLoader loader) {
			this.path = path;
			this.expected = expected;
			this.loader = loader;
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
