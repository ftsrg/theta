package hu.bme.mit.theta.xcfa.analysis.impl.lazy;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorResult;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaPrec;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;

public class LazyXcfaAbstractorConfig<SConcr extends ExprState, SAbstr extends ExprState, A extends XcfaAction, P extends Prec> {
    private final Abstractor<LazyState<XcfaState<SConcr>, XcfaState<SAbstr>>, A, XcfaPrec<P>> lazyXcfaAbstractor;
    private final XcfaPrec<P> prec;
    private ARG<LazyState<XcfaState<SConcr>, XcfaState<SAbstr>>, A> arg;

    public LazyXcfaAbstractorConfig(final Abstractor<LazyState<XcfaState<SConcr>, XcfaState<SAbstr>>, A, XcfaPrec<P>> lazyXcfaAbstractor, final XcfaPrec<P> prec) {
        this.lazyXcfaAbstractor = lazyXcfaAbstractor;
        this.prec = prec;
    }

    public AbstractorResult check() {
        arg = lazyXcfaAbstractor.createArg();
        return lazyXcfaAbstractor.check(arg, prec);
    }

    public ARG<LazyState<XcfaState<SConcr>, XcfaState<SAbstr>>, A> getArg() {
        return arg;
    }
}
