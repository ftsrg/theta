package hu.bme.mit.theta.xta.analysis.prec;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.xta.analysis.XtaState;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class GlobalXtaPrecRefiner<S extends ExprState, A extends Action, P extends Prec, R extends Refutation>
        implements PrecRefiner<XtaState<S>, A, XtaPrec<P>, R> {

    private final RefutationToPrec<P, R> refToPrec;

    private GlobalXtaPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
        this.refToPrec = checkNotNull(refToPrec);
    }

    public static <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> GlobalXtaPrecRefiner<S, A, P, R> create(
            final RefutationToPrec<P, R> refToPrec) {
        return new GlobalXtaPrecRefiner<>(refToPrec);
    }

    @Override
    public XtaPrec<P> refine(final XtaPrec<P> prec, final Trace<XtaState<S>, A> trace, final R refutation) {
        checkNotNull(trace);
        checkNotNull(prec);
        checkNotNull(refutation);
        checkArgument(prec instanceof GlobalXtaPrec); // TODO: enforce this in a
        // better way

        final GlobalXtaPrec<P> constPrec = (GlobalXtaPrec<P>) prec;
        P runningPrec = constPrec.getPrec();
        for (int i = 0; i < trace.getStates().size(); ++i) {
            final P precFromRef = refToPrec.toPrec(refutation, i);
            runningPrec = refToPrec.join(runningPrec, precFromRef);
        }
        return constPrec.refine(runningPrec);
    }

    @Override
    public String toString() {
        return getClass().getSimpleName();
    }

}

