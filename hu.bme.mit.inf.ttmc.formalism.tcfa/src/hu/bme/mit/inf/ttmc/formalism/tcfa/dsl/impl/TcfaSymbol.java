package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl;

import java.util.List;

import hu.bme.mit.inf.ttmc.common.dsl.Scope;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.dsl.ParametricSymbol;

final class TcfaSymbol extends ParametricSymbol {

	public TcfaSymbol(final Scope enclosingScope, final String name, final List<? extends ParamDecl<?>> paramDecls) {
		super(enclosingScope, name, paramDecls);
	}

}
