package hu.bme.mit.inf.theta.formalism.sts.dsl.impl;

import java.util.List;

import hu.bme.mit.inf.theta.core.decl.ParamDecl;
import hu.bme.mit.inf.theta.core.dsl.ParametricSymbol;

final class StsSpecSymbol extends ParametricSymbol {

	public StsSpecSymbol(final String name, final List<? extends ParamDecl<?>> paramDecls) {
		super(name, paramDecls, null);

	}

}
