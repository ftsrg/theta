package hu.bme.mit.theta.formalism.tcfa.dsl;

import java.util.List;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.ParametricSymbol;

final class TcfaSpecSymbol extends ParametricSymbol {

	public TcfaSpecSymbol(final String name, final List<? extends ParamDecl<?>> paramDecls) {
		super(name, paramDecls, null);

	}

}
