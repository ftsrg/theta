package hu.bme.mit.theta.analysis.itp;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public class ItpAnalysis<SConcr extends State, SAbstr extends ExprState, A extends Action, P extends Prec> implements Analysis<ItpState<SConcr, SAbstr>, A, P> {

    private final ItpOrd<SConcr, SAbstr> partialOrd;
    private final ItpInitFunc<SConcr, SAbstr, P> initFunc;
    private final ItpTransFunc<SConcr, SAbstr, A, P> transFunc;

    private ItpAnalysis(final PartialOrd<SAbstr> abstrOrd,
                       final InitFunc<SConcr, P> concrInitFunc,
                       final TransFunc<SConcr, A, P> concrTransFunc,
                       final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        checkNotNull(abstrOrd);
        checkNotNull(concrInitFunc);
        checkNotNull(concrTransFunc);
        checkNotNull(initAbstractor);
        this.partialOrd = ItpOrd.create(abstrOrd);
        this.initFunc = ItpInitFunc.create(concrInitFunc, initAbstractor);
        this.transFunc = ItpTransFunc.create(concrTransFunc, initAbstractor);
    }

    public static <SConcr extends State, SAbstr extends ExprState, A extends Action, P extends Prec> ItpAnalysis<SConcr, SAbstr, A, P>
    create(final PartialOrd<SAbstr> abstrPartialOrd,
           final InitFunc<SConcr, P> concrInitFunc,
           final TransFunc<SConcr, A, P> concrTransFunc,
           final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        return new ItpAnalysis<>(abstrPartialOrd, concrInitFunc, concrTransFunc, initAbstractor);
    }

    @Override
    public PartialOrd<ItpState<SConcr, SAbstr>> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public InitFunc<ItpState<SConcr, SAbstr>, P> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<ItpState<SConcr, SAbstr>, A, P> getTransFunc() {
        return transFunc;
    }
}
