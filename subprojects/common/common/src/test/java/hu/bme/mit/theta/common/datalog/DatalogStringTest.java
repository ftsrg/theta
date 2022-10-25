/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.common.datalog;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.Collection;
import java.util.Set;
import java.util.stream.Collectors;

@RunWith(value = Parameterized.class)
public final class DatalogStringTest {
	@Parameterized.Parameter
	public String name;

	@Parameterized.Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{
				{"succ"},
				{"trains"}    //this benchmark is from the exercise in http://ysangkok.github.io/mitre-datalog.js/wrapper.html
		});
	}

	@Test
	public void test() {
		final InputStream inStream = getClass().getResourceAsStream("/datalog/in/" + name + ".datalog");
		final InputStream outStream = getClass().getResourceAsStream("/datalog/out/" + name + ".output");

		String input = new BufferedReader(new InputStreamReader(inStream)).lines().collect(Collectors.joining());
		Set<String> output = new BufferedReader(new InputStreamReader(outStream)).lines().collect(Collectors.toSet());

		String[] s = Datalog.runProgram(input).split("\r\n");
		for (String s1 : s) {
			Assert.assertTrue(output.contains(s1));
			output.remove(s1);
		}
		Assert.assertTrue(output.isEmpty());

	}

}
