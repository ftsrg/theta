package hu.bme.mit.inf.theta.formalism.tcfa.dsl.impl;

import java.util.List;

import hu.bme.mit.inf.theta.core.decl.ParamDecl;
import hu.bme.mit.inf.theta.core.dsl.ParametricSymbol;

final class TcfaSpecSymbol extends ParametricSymbol {

	public TcfaSpecSymbol(final String name, final List<? extends ParamDecl<?>> paramDecls) {
		super(name, paramDecls, null);

	}

}
