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
package hu.bme.mit.theta.xcfa.alt.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.alt.transform.DefaultTransformation;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;

@RunWith(Parameterized.class)
public class ExplicitCheckerTest {
	@Parameter()
	public String filepath;

	@Parameter(1)
	public Boolean shouldWork;

	@Parameters()
	public static Collection<Object[]> data() {
		return FileListHelper.tests("All");
	}

	@Test
	public void test() throws IOException {
		System.out.println("Testing " + filepath);
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		XCFA xcfa = XcfaDslManager.createXcfa(inputStream);
		var checker = XcfaChecker.createChecker(xcfa, XcfaChecker.getSimpleExplicit().build());
		Assert.assertTrue(checker instanceof ExplicitChecker);
		SafetyResult<? extends State, ? extends Action> result = checker.check();
		Helper.checkResult(result, shouldWork);
	}

}
