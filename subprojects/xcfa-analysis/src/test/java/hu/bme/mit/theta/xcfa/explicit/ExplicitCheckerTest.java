package hu.bme.mit.theta.xcfa.explicit;

import com.google.common.base.Preconditions;
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

	@Parameter(1)
	public Boolean shouldWork;

	@Parameter(2)
	public Boolean traced;

	@Parameters()
	public static Collection<Object[]> data() {
		return Arrays.asList(
				new Object[]{"/functions-global-local.xcfa", true, true},
				new Object[]{"/fibonacci.xcfa", true, false},
				new Object[]{"/simple-test.xcfa", true, false},
				new Object[]{"/deadlock.xcfa", false, false},
				new Object[]{"/deadlock.xcfa", false, true},
				new Object[]{"/atomic.xcfa", true, true},
				new Object[]{"/gcd.xcfa", true, true},
				new Object[]{"/partialorder-test.xcfa", false, true},
				new Object[]{"/infiniteloop.xcfa", true, true}
				//, new Object[]{"/very-parallel.xcfa"}
		);
	}

	@Test
	public void test() throws IOException {
		System.out.println("Testing " + filepath);
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		XCFA xcfa = XcfaDslManager.createXcfa(inputStream);
		ExplicitChecker checker = new ExplicitChecker();
		ExplicitChecker.SafetyResult result = checker.check(xcfa, traced);
		if (traced) {
			Preconditions.checkState(result.safe || result.trace != null, "Tracing does not work");
		} else {
			Preconditions.checkState(result.trace == null, "Tracing when we should not");
		}

		if (!result.safe) {
			System.err.println("Safety result:");
			System.err.println(result);
		}
		if (shouldWork && !result.safe) {
			throw new RuntimeException("Error reached, but it shouldn't have been. Error: " + result.message);
		} else if (!shouldWork && result.safe) {
			throw new RuntimeException("Error or deadlock is not reached, but it should have been.");
		}
	}

}
