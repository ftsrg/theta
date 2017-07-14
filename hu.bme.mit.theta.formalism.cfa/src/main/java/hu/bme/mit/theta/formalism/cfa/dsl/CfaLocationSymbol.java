package hu.bme.mit.theta.formalism.cfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;
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

	public CfaLoc intantiate(final CFA cfa) {
		final CfaLoc loc = cfa.createLoc(name);

		if (init) {
			cfa.setInitLoc(loc);
		} else if (finall) {
			cfa.setFinalLoc(loc);
		} else if (error) {
			cfa.setErrorLoc(loc);
		}

		return loc;
	}

}
