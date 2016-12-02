package hu.bme.mit.theta.formalism.tcfa.dsl;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
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

	public static TcfaSpec createTcfaSpec(final String filepath, final List<? extends Expr<?>> params)
			throws FileNotFoundException, IOException {
		final ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filepath));

		final TcfaDslLexer lexer = new TcfaDslLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final TcfaDslParser parser = new TcfaDslParser(tokens);

		final TcfaSpecContext ctx = parser.tcfaSpec();
		final TcfaSpecSymbol tcfaSpecSymbol = TcfaSpecSymbol.create(ctx);
		final TcfaSpec tcfaSpec = tcfaSpecSymbol.instantiate(params);

		return tcfaSpec;
	}

	public static TcfaSpec createTcfaSpec(final String filepath, final Expr<?>... params)
			throws FileNotFoundException, IOException {
		return createTcfaSpec(filepath, Arrays.asList(params));
	}

}
