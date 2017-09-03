package hu.bme.mit.theta.formalism.cfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.LocContext;

final class CfaLocationSymbol implements Symbol {

	private final boolean init;
	private final boolean finall;
	private final boolean error;
	private final String name;

	public CfaLocationSymbol(final LocContext context) {
		checkNotNull(context);
		init = (context.init != null);
		finall = (context.finall != null);
		error = (context.error != null);
		name = context.id.getText();
	}

	@Override
	public String getName() {
		return name;
	}

	public boolean isInit() {
		return init;
	}

	public boolean isFinal() {
		return finall;
	}

	public boolean isError() {
		return error;
	}

	public Loc intantiate(final CFA.Builder cfaBuilder) {
		final Loc loc = cfaBuilder.createLoc(name);

		if (init) {
			cfaBuilder.setInitLoc(loc);
		} else if (finall) {
			cfaBuilder.setFinalLoc(loc);
		} else if (error) {
			cfaBuilder.setErrorLoc(loc);
		}

		return loc;
	}

}
