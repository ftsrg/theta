package hu.bme.mit.theta.xta.analysis.config;

import hu.bme.mit.theta.analysis.Cex;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.algorithm.Proof;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;

public final class XtaConfig <Pr extends Proof, C extends Cex, P extends Prec> {

    private final SafetyChecker<Pr, C, P> checker;
    private final P initPrec;

    private XtaConfig(final SafetyChecker<Pr, C, P> checker, final P initPrec) {
        this.checker = checker;
        this.initPrec = initPrec;
    }
    public static <Pr extends Proof, C extends Cex, P extends Prec> XtaConfig<Pr, C, P> create(
            final SafetyChecker<Pr, C, P> checker, final P initPrec) {
        return new XtaConfig<>(checker, initPrec);
    }

    public SafetyResult<Pr, C> check() {
        return checker.check(initPrec);
    }
}
