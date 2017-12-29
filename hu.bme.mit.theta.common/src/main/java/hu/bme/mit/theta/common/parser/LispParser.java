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

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.parser.SExpr.SAtom;
import hu.bme.mit.theta.common.parser.SExpr.SList;

public final class LispParser {

	private final LispLexer lexer;
	private Token lookahead; // use lookahead() to get value

	public LispParser(final LispLexer lexer) {
		this.lexer = checkNotNull(lexer);
		this.lookahead = null;
	}

	public List<SExpr> sexprs() {
		final ImmutableList.Builder<SExpr> builder = ImmutableList.builder();
		while (lookahead().getType() != TokenType.RPAREN) {
			final SExpr sexpr = sexpr();
			builder.add(sexpr);
		}
		return builder.build();
	}

	public SExpr sexpr() {
		if (lookahead().getType() == TokenType.ATOM) {
			return atom();
		} else if (lookahead().getType() == TokenType.LPAREN) {
			return list();
		} else {
			throw new ParserException("Expecting atom or list, found " + lookahead.getType());
		}
	}

	public SAtom atom() {
		final String atom = lookahead().getString();
		match(TokenType.ATOM);
		return SExpr.atom(atom);
	}

	public SList list() {
		match(TokenType.LPAREN);
		final List<SExpr> sexprs = sexprs();
		match(TokenType.RPAREN);
		return SExpr.list(sexprs);
	}

	private Token lookahead() {
		Token result = lookahead;
		if (result == null) {
			result = lexer.nextToken();
			lookahead = result;
		}
		return result;
	}

	private void match(final TokenType type) {
		if (lookahead().getType() == type) {
			consume();
		} else {
			throw new ParserException("Expecting " + type + ", found " + lookahead.getType());
		}
	}

	private void consume() {
		if (lookahead == null) {
			lookahead();
		}
		lookahead = null;
	}

}
