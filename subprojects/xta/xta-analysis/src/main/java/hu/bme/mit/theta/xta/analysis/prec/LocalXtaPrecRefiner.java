package hu.bme.mit.theta.xta.analysis.prec;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.analysis.XtaState;

import java.util.HashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class LocalXtaPrecRefiner <S extends ExprState, A extends Action, P extends Prec, R extends Refutation>
        implements PrecRefiner<XtaState<S>, A, XtaPrec<P>, R> {


    private final RefutationToPrec<P, R> refToPrec;


    private LocalXtaPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
        this.refToPrec = checkNotNull(refToPrec);
    }

    public static <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> LocalXtaPrecRefiner<S, A, P, R> create(
            final RefutationToPrec<P, R> refToPrec) {
        return new LocalXtaPrecRefiner<>(refToPrec);
    }

    @Override
    public XtaPrec<P> refine(XtaPrec<P> prec, Trace<XtaState<S>, A> trace, R refutation) {
        checkNotNull(trace);
        checkNotNull(prec);
        checkNotNull(refutation);
        checkArgument(prec instanceof LocalXtaPrec);



        final LocalXtaPrec<P> genPrec = (LocalXtaPrec<P>) prec;
        final Map<XtaProcess.Loc, P> runningPrecs = Containers.createMap();
        for (final XtaState<S> state : trace.getStates()) {
            for (XtaProcess.Loc l: state.getLocs())
                runningPrecs.put(l, genPrec.getPrec(state.getLocs()));

        }

        for (int i = 0; i < trace.getStates().size(); ++i) {
            for(final XtaProcess.Loc loc: trace.getState(i).getLocs()){
                final  P precForLoc = runningPrecs.get(loc);
                final P newPrecForLoc = refToPrec.toPrec(refutation, i);
                runningPrecs.put(loc, refToPrec.join(precForLoc, newPrecForLoc));
            }
        }
        return  genPrec.refine(runningPrecs);
    }
}
