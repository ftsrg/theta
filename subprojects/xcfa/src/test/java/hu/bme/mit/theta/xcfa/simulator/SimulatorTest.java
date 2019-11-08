package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

@RunWith(Parameterized.class)
public class SimulatorTest {

	@Parameter()
	public String filepath;

	@Parameters()
	public static Collection<Object[]> data() {
		return Arrays.asList(
				new Object[]{"/functions-global-local.xcfa"},
				new Object[]{"/simple-test.xcfa"}
		);
	}

	@Test
	public void test() throws IOException {
		System.out.println(new File(".").getAbsolutePath());
		//final InputStream inputStream = new FileInputStream("/home/rl/cpp/theta-xcfa/theta/out/test/theta/peterson.xcfa");
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		XCFA xcfa = XcfaDslManager.createXcfa(inputStream);
		new Simulator(xcfa);
	}
}
