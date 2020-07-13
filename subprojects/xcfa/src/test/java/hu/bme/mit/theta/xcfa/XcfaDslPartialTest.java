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
package hu.bme.mit.theta.xcfa;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.cfa.dsl.CfaWriter;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import hu.bme.mit.theta.xcfa.tocfa.Xcfa2Cfa;
import hu.bme.mit.theta.xcfa.utils.XcfaEdgeSplitterTransformation;

@RunWith(Parameterized.class)
public final class XcfaDslPartialTest {

	@Parameter(0)
	public String[] filepaths;

	@Parameters()
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{
				{
					new String[] {"/partial/rteapi_stub.xcfa", "/partial/ruOk.xcfa"},
				},
				{
					new String[] {"/partial/rteapi_stub.xcfa", "/partial/ruOkDouble.xcfa"}
				}
		});
	}

	@Test
	public void test() throws IOException {
		var streams = new ArrayList<InputStream>();
		for (String path : filepaths) {
			streams.add(getClass().getResourceAsStream(path));
		}
		XCFA _xcfa = XcfaDslManager.createXcfa(streams);
		var xcfa = XcfaEdgeSplitterTransformation.transform(_xcfa);
		var cfa = Xcfa2Cfa.toCfa(xcfa);
		CfaWriter.write(cfa, System.out);
	}

}
