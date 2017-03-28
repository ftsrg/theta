package hu.bme.mit.theta.frontend.benchmark.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.analysis.xta.algorithm.itp.XtaItpChecker;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class XtaConfiguration {

	public static enum Algorithm {
		ITP, EXTRA, LU, IPT_EXTRA, ITP_LU
	}

	private final SafetyChecker<? extends XtaState<?>, XtaAction, UnitPrec> checker;

	private XtaConfiguration(final XtaSystem system, final Predicate<? super List<? extends Loc>> errorLocs,
			final Algorithm algorithm, final SearchStrategy strategy) {
		checkNotNull(system);
		checkNotNull(errorLocs);
		checkNotNull(algorithm);
		checkNotNull(strategy);

		switch (algorithm) {
		case ITP:
			checker = XtaItpChecker.create(system, errorLocs, strategy);
			break;
		default:
			throw new AssertionError();
		}
	}

	public static XtaConfiguration create(final XtaSystem system,
			final Predicate<? super List<? extends Loc>> errorLocs, final Algorithm algorithm,
			final SearchStrategy strategy) {
		return new XtaConfiguration(system, errorLocs, algorithm, strategy);
	}

	public SafetyChecker<? extends XtaState<?>, XtaAction, UnitPrec> getChecker() {
		return checker;
	}

}
