package hu.bme.mit.theta.xta.analysis.lazy;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyChecker;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;

public class LazyXtaCheckerConfig<SConcr extends State, SAbstr extends State, P extends Prec> {

    private final LazyChecker<SConcr, SAbstr, XtaState<SConcr>, XtaState<SAbstr>, XtaAction, P> lazyXtaChecker;
    private final P prec;
    private ARG<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> arg;

    public LazyXtaCheckerConfig(final LazyChecker<SConcr, SAbstr, XtaState<SConcr>, XtaState<SAbstr>, XtaAction, P> lazyXtaChecker,
                                final P prec) {
        this.lazyXtaChecker = lazyXtaChecker;
        this.prec = prec;
    }

    public SafetyResult<ARG<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction>, Trace<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction>>
    check() {
        return lazyXtaChecker.check(prec);
    }
}
