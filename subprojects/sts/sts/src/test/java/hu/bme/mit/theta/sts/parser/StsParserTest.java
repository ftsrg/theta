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
package hu.bme.mit.theta.sts.parser;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.Arrays;
import java.util.Collection;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.sts.STS;

@RunWith(Parameterized.class)
public final class StsParserTest {

	@Parameter(0)
	public String filepath;

	@Parameter(1)
	public int vars;

	private Reader reader;
	private StsParser parser;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{"src/test/resources/simple1.lisp.sts", 2},

				{"src/test/resources/readerswriters.lisp.sts", 3},

		});
	}

	@Before
	public void before() throws FileNotFoundException {
		reader = new FileReader(filepath);
		parser = new StsParser(reader);
	}

	@After
	public void after() throws IOException {
		reader.close();
	}

	@Test
	public void test() {
		// Act
		final STS sts = parser.sts();
		System.out.println(sts);
		Assert.assertEquals(vars, sts.getVars().size());
	}

}
