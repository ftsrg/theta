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
package hu.bme.mit.theta.formalism.cfa.dsl;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslLexer;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.SpecContext;

public final class CfaDslManager {

	private CfaDslManager() {
	}

	public static CFA createCfa(final InputStream inputStream) throws FileNotFoundException, IOException {
		final ANTLRInputStream input = new ANTLRInputStream(inputStream);

		final CfaDslLexer lexer = new CfaDslLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final CfaDslParser parser = new CfaDslParser(tokens);

		final SpecContext context = parser.spec();
		final CfaSpecification specification = CfaSpecification.fromContext(context);
		final CFA cfa = specification.instantiate();
		return cfa;
	}

}
