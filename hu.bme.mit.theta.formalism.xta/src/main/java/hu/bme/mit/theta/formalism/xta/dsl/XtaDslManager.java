package hu.bme.mit.theta.formalism.xta.dsl;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslLexer;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.XtaContext;

public final class XtaDslManager {

	private XtaDslManager() {
	}

	public static void createXta(final InputStream inputStream) throws FileNotFoundException, IOException {
		final ANTLRInputStream input = new ANTLRInputStream(inputStream);

		final XtaDslLexer lexer = new XtaDslLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final XtaDslParser parser = new XtaDslParser(tokens);

		final XtaContext xtaCtx = parser.xta();
		System.out.println(xtaCtx.toStringTree(parser));
	}
}
