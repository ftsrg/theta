package hu.bme.mit.theta.formalism.tcfa.dsl;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.List;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslLexer;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.TcfaSpecContext;

public final class TcfaDslManager {

	private TcfaDslManager() {
	}

	public static TcfaSpec createTcfaSpec(final InputStream inputStream, final List<? extends Expr<?>> args)
			throws FileNotFoundException, IOException {
		final ANTLRInputStream input = new ANTLRInputStream(inputStream);

		final TcfaDslLexer lexer = new TcfaDslLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final TcfaDslParser parser = new TcfaDslParser(tokens);

		final TcfaSpecContext ctx = parser.tcfaSpec();
		final TcfaSpecSymbol tcfaSpecSymbol = TcfaSpecSymbol.create(ctx);
		final TcfaSpec tcfaSpec = tcfaSpecSymbol.instantiate(args);

		return tcfaSpec;
	}

	public static TcfaSpec createTcfaSpec(final InputStream inputStream, final Expr<?>... args)
			throws FileNotFoundException, IOException {
		return createTcfaSpec(inputStream, Arrays.asList(args));
	}

}
