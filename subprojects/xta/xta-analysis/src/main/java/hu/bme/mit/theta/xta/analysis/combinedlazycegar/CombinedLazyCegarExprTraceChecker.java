package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;

import java.util.stream.Stream;

import static hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaUtils.forceCast;

final class CombinedLazyCegarExprTraceChecker<R extends Refutation> implements ExprTraceChecker<R> {
    private final ExprTraceChecker<R> exprTraceChecker;
    private final Lens<LazyState<XtaState<Prod2State<ExplState, ZoneState>>, XtaState<Prod2State<ExplState, ZoneState>>>, Prod2State<ExplState, ZoneState>> concrProd2Lens;
    private final XtaSystem system;

    public CombinedLazyCegarExprTraceChecker(
        final ExprTraceChecker<R> exprTraceChecker,
        final Lens<LazyState<XtaState<Prod2State<ExplState, ZoneState>>, XtaState<Prod2State<ExplState, ZoneState>>>, Prod2State<ExplState, ZoneState>> concrProd2Lens,
        final XtaSystem system) {
        this.exprTraceChecker = exprTraceChecker;
        this.concrProd2Lens = concrProd2Lens;
        this.system = system;
    }

    @Override
    public ExprTraceStatus<R> check(Trace<? extends ExprState, ? extends ExprAction> trace) {
        final Trace<LazyState<XtaState<Prod2State<ExplState, ZoneState>>, XtaState<Prod2State<ExplState, ZoneState>>>, XtaAction> typedTrace = forceCast(trace);

        final var newTrace = Trace.of(
            Streams.concat(
                valuationToExprState(
                    MutableValuation.copyOf(
                        concrProd2Lens.get(typedTrace.getStates().get(0)).getState1().getVal()
                    ).putAll(system.getInitVal())
                ),
                typedTrace.getStates().stream().skip(1).map(s -> concrProd2Lens.get(s).getState1())
            ).toList(),
            typedTrace.getActions()
        );

        return exprTraceChecker.check(newTrace);
    }

    private Stream<ExprState> valuationToExprState(final Valuation valuation) {
        return Stream.of(new ExprState() {
            @Override
            public Expr<BoolType> toExpr() {
                return valuation.toExpr();
            }

            @Override
            public boolean isBottom() {
                return false;
            }
        });
    }
}
