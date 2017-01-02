package hu.bme.mit.theta.formalism.sts.dsl;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.List;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslLexer;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.StsSpecContext;

public final class StsDslManager {

	private StsDslManager() {
	}

	public static StsSpec createStsSpec(final InputStream inputStream, final List<? extends Expr<?>> args)
			throws FileNotFoundException, IOException {
		final ANTLRInputStream input = new ANTLRInputStream(inputStream);

		final StsDslLexer lexer = new StsDslLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final StsDslParser parser = new StsDslParser(tokens);

		final StsSpecContext ctx = parser.stsSpec();
		final StsSpecSymbol stsSpecSymbol = StsSpecSymbol.create(ctx);
		final StsSpec stsSpec = stsSpecSymbol.instantiate(args);

		return stsSpec;
	}

	public static StsSpec createStsSpec(final InputStream inputStream, final Expr<?>... params)
			throws FileNotFoundException, IOException {
		return createStsSpec(inputStream, Arrays.asList(params));
	}

}
