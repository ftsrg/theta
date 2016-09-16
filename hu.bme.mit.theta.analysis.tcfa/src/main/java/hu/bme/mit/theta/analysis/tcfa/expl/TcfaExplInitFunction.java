package hu.bme.mit.theta.analysis.tcfa.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.model.impl.Valuation;

public final class TcfaExplInitFunction implements InitFunction<ExplState, ExplPrecision> {

	private static final TcfaExplInitFunction INSTANCE = new TcfaExplInitFunction();

	private TcfaExplInitFunction() {
	}

	public static TcfaExplInitFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ExplState> getInitStates(final ExplPrecision precision) {
		checkNotNull(precision);
		return Collections.singleton(ExplState.create(Valuation.builder().build()));
	}

}
