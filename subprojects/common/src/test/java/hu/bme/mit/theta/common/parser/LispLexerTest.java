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
import static org.junit.Assert.assertEquals;

import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public final class LispLexerTest {
	private static final Token LPAREN = Token.of("(", TokenType.LPAREN);
	private static final Token RPAREN = Token.of(")", TokenType.RPAREN);
	private static final Token ATOM1 = Token.of("atom1", TokenType.ATOM);
	private static final Token ATOM2 = Token.of("atom2", TokenType.ATOM);
	private static final Token ATOM3 = Token.of("atom3", TokenType.ATOM);

	@Parameter(0)
	public String string;

	@Parameter(1)
	public List<Token> tokens;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "", of() },

				{ ";", of() },

				{ ";;", of() },

				{ "; comment", of() },

				{ "atom1", of(ATOM1) },

				{ "(", of(LPAREN) },

				{ ")", of(RPAREN) },

				{ "()", of(LPAREN, RPAREN) },

				{ "( )", of(LPAREN, RPAREN) },

				{ "( )", of(LPAREN, RPAREN) },

				{ "() ; comment", of(LPAREN, RPAREN) },

				{ "(atom1)", of(LPAREN, ATOM1, RPAREN) },

				{ "(atom1 atom2)", of(LPAREN, ATOM1, ATOM2, RPAREN) },

				{ "(atom1 atom2 atom3)", of(LPAREN, ATOM1, ATOM2, ATOM3, RPAREN) },

				{ "(atom1 atom2 atom3) ; comment", of(LPAREN, ATOM1, ATOM2, ATOM3, RPAREN) },

				{ "(atom1 (atom2 atom3))", of(LPAREN, ATOM1, LPAREN, ATOM2, ATOM3, RPAREN, RPAREN) },

				{ "(()(()", of(LPAREN, LPAREN, RPAREN, LPAREN, LPAREN, RPAREN) },

		});
	}

	@Test
	public void test() {
		// Arrange
		final Reader reader = new StringReader(string);
		final LispLexer lexer = new LispLexer(reader);

		final List<Token> actTokens = new ArrayList<>();

		// Act
		Token token = lexer.nextToken();
		while (token.getType() != TokenType.EOF) {
			actTokens.add(token);
			token = lexer.nextToken();
		}

		// Assert
		assertEquals(tokens, actTokens);
	}

}
