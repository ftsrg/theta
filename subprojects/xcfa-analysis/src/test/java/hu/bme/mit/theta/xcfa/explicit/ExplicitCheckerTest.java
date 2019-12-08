package hu.bme.mit.theta.xcfa.explicit;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import hu.bme.mit.theta.xcfa.simulator.ErrorReachedException;
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

	@Parameter(1)
	public Boolean shouldWork;

	@Parameters()
	public static Collection<Object[]> data() {
		return Arrays.asList(
				new Object[]{"/functions-global-local.xcfa", true},
				new Object[]{"/fibonacci.xcfa", true},
				new Object[]{"/simple-test.xcfa", true},
				new Object[]{"/deadlock.xcfa", false},
				new Object[]{"/gcd.xcfa", true}
				//, new Object[]{"/very-parallel.xcfa"}
		);
	}

	@Test
	public void test() throws IOException {
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		XCFA xcfa = XcfaDslManager.createXcfa(inputStream);
		try {
			new ExplicitChecker(xcfa);
		} catch (ErrorReachedException rex) {
			if (shouldWork) {
				throw new RuntimeException("Error reached, but it shouldn't have been.", rex);
			}
			// Otherwise works as expected...
			return;
		}
		if (!shouldWork) {
			throw new RuntimeException("Error is not reached, but it should have been");
		}
	}

}
