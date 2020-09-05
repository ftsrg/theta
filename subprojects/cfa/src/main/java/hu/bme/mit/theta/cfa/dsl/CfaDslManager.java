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
package hu.bme.mit.theta.cfa.dsl;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslLexer;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.SpecContext;

public final class CfaDslManager {

	private CfaDslManager() {
	}

	public static CFA createCfa(final String inputString) throws IOException {
		final InputStream stream = new ByteArrayInputStream(inputString.getBytes(StandardCharsets.UTF_8.name()));
		return createCfa(stream);
	}

	public static CFA createCfa(final InputStream inputStream) throws IOException {
		final CharStream input = CharStreams.fromStream(inputStream);

		final CfaDslLexer lexer = new CfaDslLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final CfaDslParser parser = new CfaDslParser(tokens);

		final SpecContext context = parser.spec();
		final CfaSpecification specification = CfaSpecification.fromContext(context);
		final CFA cfa = specification.instantiate();
		return cfa;
	}

}
