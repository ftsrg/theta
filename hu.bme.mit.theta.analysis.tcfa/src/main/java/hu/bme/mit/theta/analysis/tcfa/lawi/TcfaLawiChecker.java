package hu.bme.mit.theta.analysis.tcfa.lawi;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.impl.ARG;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public class TcfaLawiChecker {

	private final Analysis<TcfaLawiState, TcfaAction, NullPrecision> analysis;

	public TcfaLawiChecker(final TCFA tcfa) {
		analysis = new TcfaLawiAnalysis();

	}

	public void unwind(final TCFA tcfa, final TcfaLoc target) {
		final Predicate<TcfaLawiState> targetPredicate = (s -> s.getState().getLoc().equals(target));
		@SuppressWarnings("unused")
		final ARG<TcfaLawiState, TcfaAction, NullPrecision> arg = new ARG<>(analysis, targetPredicate,
				NullPrecision.getInstance());
	}

}