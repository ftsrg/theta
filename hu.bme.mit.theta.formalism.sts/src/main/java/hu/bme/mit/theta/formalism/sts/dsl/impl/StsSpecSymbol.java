package hu.bme.mit.theta.formalism.sts.dsl.impl;

import java.util.List;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.ParametricSymbol;

final class StsSpecSymbol extends ParametricSymbol {

	public StsSpecSymbol(final String name, final List<? extends ParamDecl<?>> paramDecls) {
		super(name, paramDecls, null);

	}

}
