package hu.bme.mit.theta.analysis.tcfa.expl;

import static hu.bme.mit.theta.core.expr.impl.Exprs.False;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.Type;

final class TcfaExplInitFunction implements InitFunction<ExplState, ExplPrec> {

	private static final TcfaExplInitFunction INSTANCE = new TcfaExplInitFunction();

	private TcfaExplInitFunction() {
	}

	public static TcfaExplInitFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<? extends ExplState> getInitStates(final ExplPrec prec) {
		final Valuation.Builder builder = Valuation.builder();
		for (final VarDecl<?> varDecl : prec.getVars()) {
			final Type type = varDecl.getType();
			if (type instanceof BoolType) {
				builder.put(varDecl, False());
			} else if (type instanceof IntType) {
				builder.put(varDecl, Int(0));
			} else {
				throw new UnsupportedOperationException();
			}
		}
		final Valuation valuation = builder.build();
		return Collections.singleton(ExplState.create(valuation));
	}

}
