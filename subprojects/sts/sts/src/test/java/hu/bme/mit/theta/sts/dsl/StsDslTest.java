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
package hu.bme.mit.theta.sts.dsl;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.sts.STS;

@RunWith(Parameterized.class)
public class StsDslTest {

	@Parameter(0)
	public String filepath;

	@Parameter(1)
	public String propertyName;

	@Parameter(2)
	public int varCount;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{"/readerswriters.system", "safe", 3},

				{"/simple1.system", "safe", 2}

		});
	}

	@Test
	public void test() throws FileNotFoundException, IOException {
		final InputStream inputStream = StsDslTest.class.getResourceAsStream(filepath);
		final StsSpec spec = StsDslManager.createStsSpec(inputStream);
		final STS sts = spec.createProp(propertyName);
		Assert.assertEquals(varCount, sts.getVars().size());
	}

}
