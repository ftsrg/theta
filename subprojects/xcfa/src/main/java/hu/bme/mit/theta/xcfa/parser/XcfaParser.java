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
package hu.bme.mit.theta.xcfa.parser;

import static com.google.common.base.Preconditions.checkNotNull;

import java.io.Reader;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.common.parser.LispLexer;
import hu.bme.mit.theta.common.parser.LispParser;
import hu.bme.mit.theta.common.parser.SExpr;
import hu.bme.mit.theta.core.parser.Env;

public final class XcfaParser {

	private final LispParser parser;
	private final XcfaInterpreter interpreter;

	public XcfaParser(final Reader reader) {
		checkNotNull(reader);
		final LispLexer lexer = new LispLexer(reader);
		parser = new LispParser(lexer);
		final Env env = new Env();
		interpreter = new XcfaInterpreter(env);
	}

	public XCFA xcfa() {
		final SExpr sexpr = parser.sexpr();
		final XCFA xcfa = interpreter.xcfa(sexpr);
		return xcfa;
	}

}
