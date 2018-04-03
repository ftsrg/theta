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
package hu.bme.mit.theta.core.parser;

import static com.google.common.base.Preconditions.checkNotNull;

import java.io.Reader;

import hu.bme.mit.theta.common.parser.LispLexer;
import hu.bme.mit.theta.common.parser.LispParser;
import hu.bme.mit.theta.common.parser.SExpr;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class CoreParser {

	private final LispParser parser;
	private final CoreInterpreter interpreter;

	public CoreParser(final Reader reader) {
		checkNotNull(reader);
		final LispLexer lexer = new LispLexer(reader);
		parser = new LispParser(lexer);
		final Env env = new Env();
		interpreter = new CoreInterpreter(env);
		interpreter.defineCommonTypes();
		interpreter.defineCommonExprs();
		interpreter.defineCommonStmts();
	}

	public void declare(final Decl<?> decl) {
		interpreter.declare(decl);
	}

	public Type type() {
		final SExpr sexpr = parser.sexpr();
		final Type type = interpreter.type(sexpr);
		return type;
	}

	public Expr<?> expr() {
		final SExpr sexpr = parser.sexpr();
		final Expr<?> expr = interpreter.expr(sexpr);
		return expr;
	}

	public Stmt stmt() {
		final SExpr sexpr = parser.sexpr();
		final Stmt stmt = interpreter.stmt(sexpr);
		return stmt;
	}

}
