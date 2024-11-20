package hu.bme.mit.theta.xsts.analysis.timed;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.xsts.analysis.XstsAction;
import hu.bme.mit.theta.xsts.analysis.XstsState;
import hu.bme.mit.theta.xsts.analysis.timed.TimedXstsActionProjections;

public final class XstsCombinedExprTraceChecker <R extends Refutation> implements ExprTraceChecker<R> {

    private final ExprTraceChecker<R> exprTraceChecker;
    private final Lens<LazyState<XstsState<Prod2State<? extends ExprState, ?>>, XstsState<Prod2State<? extends ExprState, ?>>>, Prod2State<? extends ExprState, ?>> concrProd2Lens;
    private final TimedXstsActionProjections timedXstsActionProjections;

    public XstsCombinedExprTraceChecker(
            final ExprTraceChecker<R> exprTraceChecker,
            final Lens<LazyState<XstsState<Prod2State<? extends ExprState, ?>>, XstsState<Prod2State<? extends ExprState, ?>>>, Prod2State<? extends ExprState, ?>> concrProd2Lens,
            final TimedXstsActionProjections timedXstsActionProjections) {
        this.exprTraceChecker = exprTraceChecker;
        this.concrProd2Lens = concrProd2Lens;
        this.timedXstsActionProjections = timedXstsActionProjections;
    }

    @Override
    public ExprTraceStatus<R> check(Trace<? extends ExprState, ? extends ExprAction> trace) {
        final Trace<LazyState<XstsState<Prod2State<? extends ExprState, ?>>, XstsState<Prod2State<? extends ExprState, ?>>>, XstsAction>
                typedTrace = (Trace<LazyState<XstsState<Prod2State<? extends ExprState, ?>>, XstsState<Prod2State<? extends ExprState, ?>>>, XstsAction>) trace;

        final var newTrace = Trace.of(
                typedTrace.getStates().stream().map(s -> concrProd2Lens.get(s).getState1()).toList(),
                typedTrace.getActions().stream().map(timedXstsActionProjections::dataProjection).toList()
        );

        return exprTraceChecker.check(newTrace);
    }
}
