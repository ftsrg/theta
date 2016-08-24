package hu.bme.mit.inf.theta.statechart.tests;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.theta.statechart.model.StatechartSpecification;
import hu.bme.mit.inf.theta.statechart.ui.StatechartModelLoader;

public class StatechartModelTests {

	@Test
	public void testMonitor() throws IOException {
		final File file = new File("instances/monitor.statechart");
		final String filePath = file.getAbsolutePath();
		final StatechartSpecification specification = StatechartModelLoader.getInstance().load(filePath);
		System.out.println(specification.getName());
	}

}
