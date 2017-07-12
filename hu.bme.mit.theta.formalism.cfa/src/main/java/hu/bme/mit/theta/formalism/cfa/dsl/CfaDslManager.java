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
