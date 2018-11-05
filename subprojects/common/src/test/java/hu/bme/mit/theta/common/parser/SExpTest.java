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
package hu.bme.mit.theta.common.parser;

import static com.google.common.collect.ImmutableList.of;
import static hu.bme.mit.theta.common.parser.SExpr.atom;
import static hu.bme.mit.theta.common.parser.SExpr.list;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public final class SExpTest {
	private static final String A = "A";
	private static final String B = "B";
	private static final String C = "C";

	@Parameter(0)
	public Object object;

	@Parameter(1)
	public SExpr sexpr;

	@Parameter(2)
	public String string;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ A, atom(A), A },

				{ of(), list(), "()" },

				{ of(A), list(atom(A)), "(A)" },

				{ of(A, B), list(atom(A), atom(B)), "(A B)" },

				{ of(A, B, C), list(atom(A), atom(B), atom(C)), "(A B C)" },

				{ of(A, of(B, C)), list(atom(A), list(atom(B), atom(C))), "(A (B C))" },

				{ of(A, B, of(C, of(A))), list(atom(A), atom(B), list(atom(C), list(atom(A)))), "(A B (C (A)))" }

		});
	}

	@Test
	public void testBuild() {
		final SExpr actSexpr = SExpr.build(object);
		assertEquals(sexpr, actSexpr);
	}

	@Test
	public void testParse() {
		final SExpr actSexpr = SExpr.parse(string);
		assertEquals(sexpr, actSexpr);
	}

	@Test
	public void testToString() {
		final String actString = sexpr.toString();
		assertEquals(string, actString);
	}

}
