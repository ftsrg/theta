package hu.bme.mit.theta.formalism.sts.dsl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import hu.bme.mit.theta.common.dsl.Scope2;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.ParametricSymbol;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.StsContext;

final class StsSymbol extends ParametricSymbol {

	private final StsContext stsCtx;

	public StsSymbol(final String name, final List<? extends ParamDecl<?>> paramDecls, final Scope2 enclosingScope,
			final StsContext stsCtx) {
		super(name, paramDecls, enclosingScope);
		this.stsCtx = checkNotNull(stsCtx);
	}

	public StsContext getStsCtx() {
		return stsCtx;
	}

}
