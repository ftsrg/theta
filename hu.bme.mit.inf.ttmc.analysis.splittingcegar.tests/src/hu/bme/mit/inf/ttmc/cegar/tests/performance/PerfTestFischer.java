package hu.bme.mit.inf.ttmc.cegar.tests.performance;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.cegar.common.ICEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.InterpolatingCEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.InterpolatingCEGARBuilder.InterpolationMethod;
import hu.bme.mit.inf.ttmc.cegar.tests.formatters.ExcelFormatter;
import hu.bme.mit.inf.ttmc.cegar.tests.formatters.IFormatter;

public class PerfTestFischer extends PerfTestBase {

	private static final int TIMEOUT = 5 * 60 * 1000;
	private static final IFormatter FORMATTER = new ExcelFormatter();

	@SuppressWarnings("serial")
	@Test
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

		run(testCases, configurations, TIMEOUT, FORMATTER);
	}

}
