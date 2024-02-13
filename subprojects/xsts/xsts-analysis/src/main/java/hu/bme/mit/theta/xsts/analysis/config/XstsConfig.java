package hu.bme.mit.theta.xsts.analysis.config;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;

public final class XstsConfig<S extends State, A extends Action, P extends Prec> {

	private final SafetyChecker<ARG<S, A>, Trace<S, A>, P> checker;
	private final P initPrec;

	private XstsConfig(final SafetyChecker<ARG<S, A>, Trace<S, A>, P> checker, final P initPrec) {
		this.checker = checker;
		this.initPrec = initPrec;
	}

	public static <S extends State, A extends Action, P extends Prec> XstsConfig<S, A, P> create(
			final SafetyChecker<ARG<S, A>, Trace<S, A>, P> checker, final P initPrec) {
		return new XstsConfig<>(checker, initPrec);
	}

	public SafetyResult<ARG<S, A>, Trace<S, A>> check() {
		return checker.check(initPrec);
	}

}