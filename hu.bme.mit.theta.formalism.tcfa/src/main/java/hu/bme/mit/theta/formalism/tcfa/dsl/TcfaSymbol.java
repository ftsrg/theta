package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.ParametricSymbol;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.TcfaContext;

final class TcfaSymbol extends ParametricSymbol {

	private final TcfaContext tcfaCtx;

	public TcfaSymbol(final String name, final List<? extends ParamDecl<?>> paramDecls, final Scope enclosingScope,
			final TcfaContext tcfaCtx) {
		super(name, paramDecls, enclosingScope);
		this.tcfaCtx = checkNotNull(tcfaCtx);
	}

	public TcfaContext getTcfaCtx() {
		return tcfaCtx;
	}

}
