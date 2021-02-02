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
package hu.bme.mit.theta.cfa.parser;

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

import hu.bme.mit.theta.cfa.CFA;

@RunWith(Parameterized.class)
public final class CfaParserTest {

	@Parameter(0)
	public String filepath;

	private Reader reader;
	private CfaParser parser;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{"src/test/resources/counter5_true.lisp.cfa"},

		});
	}

	@Before
	public void before() throws FileNotFoundException {
		reader = new FileReader(filepath);
		parser = new CfaParser(reader);
	}

	@After
	public void after() throws IOException {
		reader.close();
	}

	@Test
	public void test() {
		// Act
		final CFA cfa = parser.cfa();
		Assert.assertEquals(1, cfa.getVars().size());
		Assert.assertEquals(6, cfa.getLocs().size());
		Assert.assertEquals(6, cfa.getEdges().size());
	}

}
