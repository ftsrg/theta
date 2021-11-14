/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.cli.stateless;

import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.utils.FrontendXcfaBuilder;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkState;

@RunWith(Parameterized.class)
public class XcfaCliParseTest {
	@Parameterized.Parameter(0)
	public String filepath;

	@Parameterized.Parameters()
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{
				{"/c/dekker.i"},
				{"/c/litmustest/singlethread/00assignment.c"},
				{"/c/litmustest/singlethread/01cast.c"},
				{"/c/litmustest/singlethread/02types.c"},
				{"/c/litmustest/singlethread/03bitwise.c"},
				{"/c/litmustest/singlethread/04real.c"},
				{"/c/litmustest/singlethread/05math.c"},
				{"/c/litmustest/singlethread/06arrays.c"},
				{"/c/litmustest/singlethread/07arrayinit.c"},
				{"/c/litmustest/singlethread/08vararray.c"},
				{"/c/litmustest/singlethread/09struct.c"},
				{"/c/litmustest/singlethread/10ptr.c"},
				{"/c/litmustest/singlethread/11ptrs.c"},
				{"/c/litmustest/singlethread/12ptrtypes.c"},
				{"/c/litmustest/singlethread/13typedef.c"},
				{"/c/litmustest/singlethread/14ushort.c"},
		});
	}

	@Test
	public void test() throws IOException {
		ArchitectureConfig.arithmetic = ArchitectureConfig.ArithmeticType.efficient;
		ArchitectureConfig.multiThreading = false;
		FrontendMetadata.clear();
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		assert inputStream != null;
		final CharStream input = CharStreams.fromStream(inputStream);

		final CLexer lexer = new CLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final CParser parser = new CParser(tokens);

		final CParser.CompilationUnitContext context = parser.compilationUnit();

		CStatement program = context.accept(FunctionVisitor.instance);
		checkState(program instanceof CProgram, "Parsing did not return a program!");
		FrontendXcfaBuilder frontendXcfaBuilder = new FrontendXcfaBuilder();
		XCFA xcfa = frontendXcfaBuilder.buildXcfa((CProgram) program).build();
	}
}
