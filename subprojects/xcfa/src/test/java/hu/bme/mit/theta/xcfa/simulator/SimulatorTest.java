/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.xcfa.simulator;

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
public class SimulatorTest {

	@Parameter()
	public String filepath;

	@Parameters()
	public static Collection<Object[]> data() {
		return Arrays.asList(
				new Object[]{"/functions-global-local.xcfa"},
				new Object[]{"/fibonacci.xcfa"},
				new Object[]{"/havoc-test.xcfa"},
				new Object[]{"/simple-test.xcfa"},
				new Object[]{"/gcd.xcfa"}
		);
	}

	@Test
	public void test() throws IOException {
		//final InputStream inputStream = new FileInputStream("/home/rl/cpp/theta-xcfa/theta/out/test/theta/peterson.xcfa");
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		XCFA xcfa = XcfaDslManager.createXcfa(inputStream);
		Simulator s = new Simulator(xcfa);
		try {
			while (s.step()) {
				//
			}
		} catch (ErrorReachedException ex) {
			ex.printStackTrace();
			System.out.println("Error location reached or deadlock!");
		}
	}
}
