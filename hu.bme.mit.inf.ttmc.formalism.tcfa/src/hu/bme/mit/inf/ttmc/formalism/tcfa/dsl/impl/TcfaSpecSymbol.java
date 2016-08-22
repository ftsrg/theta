package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;

final class TcfaSpecSymbol extends ParametricSymbol {

	public TcfaSpecSymbol(final String name, final List<? extends ParamDecl<?>> paramDecls) {
		super(name, paramDecls, null);

	}

}
