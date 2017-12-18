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

import static com.google.common.base.Preconditions.checkNotNull;

import java.io.IOException;
import java.io.Reader;

public final class LispLexer {
	private static final int EOF = -1;

	private final Reader reader;
	private int c;

	public LispLexer(final Reader reader) {
		this.reader = checkNotNull(reader);
		consume();
	}

	public Token nextToken() {
		while (c != EOF) {
			switch (c) {
			case ' ':
			case '\t':
			case '\n':
			case '\r':
				WS();
				continue;
			case ';':
				COMMENT();
				continue;
			case '(':
				return LPAREN();
			case ')':
				return RPAREN();
			default:
				return ATOM();
			}
		}

		return Token.of("<EOF>", TokenType.EOF);
	}

	private Token LPAREN() {
		consume();
		return Token.of("(", TokenType.LPAREN);
	}

	private Token RPAREN() {
		consume();
		return Token.of(")", TokenType.RPAREN);
	}

	private Token ATOM() {
		final StringBuilder sb = new StringBuilder();
		while (c != ' ' && c != '\t' && c != '\n' && c != '\r' && c != ';' && c != '(' && c != ')' && c != EOF) {
			sb.append((char) c);
			consume();
		}
		return Token.of(sb.toString(), TokenType.ATOM);
	}

	private void WS() {
		while (c == ' ' || c == '\t' || c == '\n' || c == '\r') {
			consume();
		}
	}

	private void COMMENT() {
		while (c != '\n' && c != '\r' && c != EOF) {
			consume();
		}
	}

	private void consume() {
		try {
			c = reader.read();
		} catch (final IOException e) {
			throw new LexerException(e);
		}
	}

	@SuppressWarnings("unused")
	private void match(final char x) {
		if (c == x) {
			consume();
		} else {
			throw new LexerException("Expecting " + x + ", found " + c);
		}
	}

}
