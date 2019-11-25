package hu.bme.mit.theta.xcfa.explicit;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

@RunWith(Parameterized.class)
public class ExplicitCheckerTest {
	@Parameter()
	public String filepath;

	@Parameters()
	public static Collection<Object[]> data() {
		return Arrays.asList(
				new Object[]{"/functions-global-local.xcfa"},
				new Object[]{"/fibonacci.xcfa"},
				new Object[]{"/simple-test.xcfa"},
				new Object[]{"/gcd.xcfa"}
				//, new Object[]{"/very-parallel.xcfa"}
		);
	}

	@Test
	public void test() throws IOException {
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		XCFA xcfa = XcfaDslManager.createXcfa(inputStream);
		ExplicitChecker explicitChecker = new ExplicitChecker(xcfa);
	}
}
