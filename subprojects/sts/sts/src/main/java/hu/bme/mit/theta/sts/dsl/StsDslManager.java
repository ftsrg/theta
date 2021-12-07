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
package hu.bme.mit.theta.sts.dsl;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.List;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.sts.dsl.gen.StsDslLexer;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.StsSpecContext;

public final class StsDslManager {

	private StsDslManager() {
	}

	public static StsSpec createStsSpec(final String inputString, final Expr<?>... params) throws IOException {
		final InputStream stream = new ByteArrayInputStream(inputString.getBytes(StandardCharsets.UTF_8.name()));
		return createStsSpec(stream, params);
	}

	public static StsSpec createStsSpec(final InputStream inputStream, final List<? extends Expr<?>> args)
			throws IOException {
		final CharStream input = CharStreams.fromStream(inputStream);

		final StsDslLexer lexer = new StsDslLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final StsDslParser parser = new StsDslParser(tokens);

		final StsSpecContext ctx = parser.stsSpec();
		final StsSpecSymbol stsSpecSymbol = StsSpecSymbol.create(ctx);
		final StsSpec stsSpec = stsSpecSymbol.instantiate(args);

		return stsSpec;
	}

	public static StsSpec createStsSpec(final InputStream inputStream, final Expr<?>... params) throws IOException {
		return createStsSpec(inputStream, Arrays.asList(params));
	}

}
