package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslLexer;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.SpecContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl.TcfaSpec;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl.TcfaSpecCreator;

public final class TcfaDslManager {

	private TcfaDslManager() {
	}

	public static TcfaSpec parse(final String filepath) throws FileNotFoundException, IOException {
		final ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filepath));

		final TcfaDslLexer lexer = new TcfaDslLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final TcfaDslParser parser = new TcfaDslParser(tokens);

		final SpecContext ctx = parser.spec();

		final TcfaSpec spec = TcfaSpecCreator.createTcfaSpec(ctx);

		return spec;
	}

}
