package hu.bme.mit.theta.formalism.sts.dsl;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Collections;
import java.util.List;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslLexer;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.SpecContext;
import hu.bme.mit.theta.formalism.sts.dsl.impl.StsSpec;
import hu.bme.mit.theta.formalism.sts.dsl.impl.StsSpecCreator;

public final class StsDslManager {

	private StsDslManager() {
	}

	public static StsSpec parse(final String filepath) throws FileNotFoundException, IOException {
		return parse(filepath, Collections.emptyList());
	}

	public static StsSpec parse(final String filepath, final List<? extends LitExpr<?>> params)
			throws FileNotFoundException, IOException {
		final ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filepath));

		final StsDslLexer lexer = new StsDslLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final StsDslParser parser = new StsDslParser(tokens);

		final SpecContext ctx = parser.spec();

		final StsSpec spec = StsSpecCreator.createStsSpec(ctx, params);

		return spec;
	}

}
