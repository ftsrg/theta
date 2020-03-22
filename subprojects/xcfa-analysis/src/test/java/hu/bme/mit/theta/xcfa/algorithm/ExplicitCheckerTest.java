/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
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

	@Parameters()
	public static Collection<Object[]> data() {
		return Arrays.asList(
				new Object[]{"/functions-global-local.xcfa", true},
				new Object[]{"/fibonacci.xcfa", true},
				new Object[]{"/simple-test.xcfa", true},
				new Object[]{"/deadlock.xcfa", false},
				new Object[]{"/atomic.xcfa", true},
				new Object[]{"/gcd.xcfa", true},
				new Object[]{"/partialorder-test.xcfa", false},
				new Object[]{"/infiniteloop.xcfa", true},
				new Object[]{"/mutex-test.xcfa", true},
				new Object[]{"/mutex-test2.xcfa", false},
				new Object[]{"/mutex-test3.xcfa", false}
				//, new Object[]{"/very-parallel.xcfa", true}
		);
	}

	public static void checkResult(SafetyResult<? extends State, ? extends Action> result, boolean shouldWork) {
		System.err.println("Safety result: " + (result.isSafe() ? "Safe" : "Unsafe"));
		if (!result.isSafe()) {
			for (Action t: result.asUnsafe().getTrace().getActions()) {
				System.err.println(t);
			}
			/*try {
				GraphvizWriter.getInstance().writeFile(
						TraceVisualizer.getDefault().visualize(result.asUnsafe().getTrace()),
						"." + filepath + ".svg",
						GraphvizWriter.Format.SVG
				);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}*/
		}
		if (shouldWork && !result.isSafe()) {
			throw new RuntimeException("Error reached, but it shouldn't have been. Error: " + result);
		} else if (!shouldWork && result.isSafe()) {
			throw new RuntimeException("Error or deadlock is not reached, but it should have been.");
		}
	}

	@Test
	public void test() throws IOException {
		System.out.println("Testing " + filepath);
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		XCFA xcfa = XcfaDslManager.createXcfa(inputStream);
		ExplicitChecker checker = new ExplicitChecker(xcfa);
		SafetyResult<? extends State, ? extends Action> result = checker.check();
		checkResult(result, shouldWork);
	}

}
