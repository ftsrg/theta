package hu.bme.mit.theta.splittingcegar.ui.performance;

import java.util.ArrayList;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;

import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.table.impl.SimpleTableWriter;
import hu.bme.mit.theta.splittingcegar.common.CEGARBuilder;
import hu.bme.mit.theta.splittingcegar.interpolating.InterpolatingCEGARBuilder;
import hu.bme.mit.theta.splittingcegar.interpolating.InterpolatingCEGARBuilder.InterpolationMethod;

public class PerfTestFischer extends PerfTestBase {

	private static final int TIMEOUT = 5 * 60 * 1000;
	private static final TableWriter FORMATTER = new SimpleTableWriter(new ConsoleLogger(100), "\t");

	@SuppressWarnings("serial")
	@Test
	@Ignore
	public void testFischer() {
		final IModelLoader loader = new SystemFileModelLoader();

		final List<TestCase> testCases = new ArrayList<TestCase>() {
			{
				add(new TestCase("src/test/resources/models/fischer/fischer2.system", true, loader));
				add(new TestCase("src/test/resources/models/fischer/fischer2_bad.system", false, loader));
				add(new TestCase("src/test/resources/models/fischer/fischer3_bool.system", true, loader));
				add(new TestCase("src/test/resources/models/fischer/fischer3_bool_bad.system", false, loader));
			}
		};
		final List<CEGARBuilder> configurations = new ArrayList<CEGARBuilder>() {
			{
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null)
						.interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(true)
						.useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null)
						.interpolationMethod(InterpolationMethod.Sequence).incrementalModelChecking(true)
						.useCNFTransformation(false));
			}
		};

		run(testCases, configurations, TIMEOUT, FORMATTER);
	}

}
