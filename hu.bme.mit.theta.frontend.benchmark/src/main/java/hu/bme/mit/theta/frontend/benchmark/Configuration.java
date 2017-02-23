package hu.bme.mit.theta.frontend.benchmark;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;

public final class Configuration<S extends State, A extends Action, P extends Prec> {
	private final SafetyChecker<S, A, P> checker;
	private final P initPrec;

	private Configuration(final SafetyChecker<S, A, P> checker, final P initPrec) {
		this.checker = checker;
		this.initPrec = initPrec;
	}

	public static <S extends State, A extends Action, P extends Prec> Configuration<S, A, P> create(
			final SafetyChecker<S, A, P> checker, final P initPrec) {
		return new Configuration<>(checker, initPrec);
	}

	public SafetyStatus<S, A> check() {
		return checker.check(initPrec);
	}

}
