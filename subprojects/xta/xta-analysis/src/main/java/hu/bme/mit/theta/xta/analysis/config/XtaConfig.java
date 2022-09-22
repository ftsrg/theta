package hu.bme.mit.theta.xta.analysis.config;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;

public final class XtaConfig <S extends State, A extends Action, P extends Prec>{
    private final SafetyChecker<S, A, P> checker;
    private final P initPrec;
    private XtaConfig(final SafetyChecker<S, A, P> checker, final P initPrec) {
        this.checker = checker;
        this.initPrec = initPrec;
    }
    public static <S extends State, A extends Action, P extends Prec> XtaConfig<S, A, P> create(
            final SafetyChecker<S, A, P> checker, final P initPrec) {
        return new XtaConfig<>(checker, initPrec);
    }

    public SafetyResult<S, A> check() {
        return checker.check(initPrec);
    }
}
