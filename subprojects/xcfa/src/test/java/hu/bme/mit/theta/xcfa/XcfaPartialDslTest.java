/*
 *  Copyright 2020 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa;

import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;

@RunWith(Parameterized.class)
public class XcfaPartialDslTest {

	@Parameter(0)
	public String[] filepaths;

	@Parameter(1)
	public int globalVarCount;

	@Parameter(2)
	public int processCount;

	@Parameter(3)
	public Integer[] processVarCount;

	@Parameter(4)
	public Integer[] processParamCount;

	@Parameter(5)
	public Integer[] procedureCount;

	@Parameter(6)
	public Integer[][] procedureVarCount;

	@Parameter(7)
	public Integer[][] procedureParamCount;

	@Parameter(8)
	public Integer[][] locCount;

	@Parameter(9)
	public Integer[][] edgeCount;

	@Parameters()
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{new String[]{"/partial/a.xcfa", "/partial/b.xcfa"}, //filepaths
						0,                                           //globalVarCount
						1,                                           //processCount
						new Integer[]{1},                      	     //processVarCount
						new Integer[]{0},                     	     //processParamCount
						new Integer[]{2},          	                 //procedureCount
						new Integer[][]{{0, 0}},             	     //procedureVarCount
						new Integer[][]{{0, 0}},     	             //procedureParamCount
						new Integer[][]{{2, 4}},     	             //locCount
						new Integer[][]{{1, 3}},             	     //edgeCount
				}
		});
	}

	@Test
	public void test() throws IOException {
		System.err.println(filepaths[0]);
		final InputStream[] inputStreams = Arrays.stream(filepaths)
				.map(path -> getClass().getResourceAsStream(path))
				.collect(Collectors.toList()).toArray(new InputStream[0]);
		XCFA xcfa = XcfaDslManager.createXcfa(inputStreams);
		Arrays.stream(inputStreams).forEach(stream -> {
			try { stream.close(); } catch (IOException e) { throw new RuntimeException(e); }
		});
		Assert.assertEquals(globalVarCount, xcfa.getGlobalVars().size());
		Assert.assertEquals(processCount, xcfa.getProcesses().size());
		for (int i = 0; i < xcfa.getProcesses().size(); ++i) {
			XCFAProcess process = xcfa.getProcesses().get(i);
			Assert.assertEquals((long) processVarCount[i], process.getThreadLocalVars().size());
			Assert.assertEquals((long) processParamCount[i], process.getParams().size());
			Assert.assertEquals((long) procedureCount[i], process.getProcedures().size());
			for (int j = 0; j < process.getProcedures().size(); ++j) {
				XCFAProcedure procedure = process.getProcedures().get(j);
				Assert.assertEquals((long) procedureVarCount[i][j], procedure.getLocalVars().size());
				Assert.assertEquals((long) procedureParamCount[i][j], procedure.getParams().size());
				Assert.assertEquals((long) locCount[i][j], procedure.getLocs().size());
				Assert.assertEquals((long) edgeCount[i][j], procedure.getEdges().size());
			}
		}
	}

}
