package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;

import static com.google.common.base.Preconditions.checkNotNull;

final class CombinedLazyCegarXtaPrecRefiner
    <DConcr extends State, CConcr extends State, DAbstr extends ExprState, CAbstr extends ExprState, DPrec extends Prec, CPrec extends Prec, R extends Refutation>
    implements PrecRefiner<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, Prod2Prec<DPrec, CPrec>, R> {
    private final RefutationToPrec<DPrec, R> refToPrec;

    CombinedLazyCegarXtaPrecRefiner(final RefutationToPrec<DPrec, R> refToPrec) {
        this.refToPrec = refToPrec;
    }

    @Override
    public Prod2Prec<DPrec, CPrec> refine(
        final Prod2Prec<DPrec, CPrec> prec,
        final Trace<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction> trace,
        final R refutation
    ) {
        checkNotNull(trace);
        checkNotNull(prec);
        checkNotNull(refutation);
        DPrec runningPrec = prec.getPrec1();
        for (int i = 0; i < trace.getStates().size(); ++i) {
            final DPrec precFromRef = refToPrec.toPrec(refutation, i);
            runningPrec = refToPrec.join(runningPrec, precFromRef);
        }
        return Prod2Prec.of(runningPrec, prec.getPrec2());
    }
}
