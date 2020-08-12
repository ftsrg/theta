package hu.bme.mit.theta.analysis.expr.refinement;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.*;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

/**
 * An ExprTraceChecker that generates new predicates based on the UCB algorithm by
 * Leucker, Martin & Markin, Grigory & Neuhäußer, Martin. (2015). A New Refinement
 * Strategy for CEGAR-Based Industrial Model Checking. 155-170. 10.1007/978-3-319-26287-1_10.
 */
public class ExprTraceUCBChecker implements ExprTraceChecker<ItpRefutation>  {

    private final ItpSolver solver;
    private final Expr<BoolType> init;
    private final Expr<BoolType> target;

    private ExprTraceUCBChecker(final Expr<BoolType> init, final Expr<BoolType> target, final ItpSolver solver) {
        this.solver = checkNotNull(solver);
        this.init = checkNotNull(init);
        this.target = checkNotNull(target);
    }

    public static ExprTraceUCBChecker create(final Expr<BoolType> init, final Expr<BoolType> target,
                                                final ItpSolver solver) {
        return new ExprTraceUCBChecker(init, target, solver);
    }

    @Override
    public ExprTraceStatus<ItpRefutation> check(Trace<? extends ExprState, ? extends ExprAction> trace) {
        checkNotNull(trace);
        final int stateCount = trace.getStates().size();

        final List<VarIndexing> indexings = new ArrayList<>(stateCount);
        indexings.add(VarIndexing.all(0));

        Valuation model = null;
        Collection<Expr<BoolType>> unsatCore = null;
        boolean concretizable;

        try (WithPushPop wpp = new WithPushPop(solver)) {
            solver.track(ExprUtils.getConjuncts(PathUtils.unfold(init, indexings.get(0))));
            solver.track(ExprUtils.getConjuncts(PathUtils.unfold(trace.getState(0).toExpr(), indexings.get(0))));
            assert solver.check().isSat() : "Initial state of the trace is not feasible";

            for (int i = 1; i < stateCount; ++i) {
                indexings.add(indexings.get(i - 1).add(trace.getAction(i - 1).nextIndexing()));
                solver.track(ExprUtils.getConjuncts(PathUtils.unfold(trace.getState(i).toExpr(), indexings.get(i))));
                solver.track(ExprUtils
                        .getConjuncts(PathUtils.unfold(trace.getAction(i - 1).toExpr(), indexings.get(i - 1))));
            }

            solver.track(ExprUtils.getConjuncts(PathUtils.unfold(target, indexings.get(stateCount - 1))));
            concretizable = solver.check().isSat();

            if (concretizable) {
                model = solver.getModel();
            } else {
                unsatCore = solver.getUnsatCore();
            }
        }

        if (concretizable) {
            checkNotNull(model);
            return createCounterexample(model, indexings, trace);
        } else {
            checkNotNull(unsatCore);
            return createRefinement(unsatCore, indexings, trace);
        }
    }

    @Override
    public String toString() {
        return getClass().getSimpleName();
    }

    private ExprTraceStatus.Feasible<ItpRefutation> createCounterexample(
        final Valuation model,
        final List<VarIndexing> indexings,
        final Trace<? extends ExprState, ? extends ExprAction> trace
    ) {
        final ImmutableList.Builder<Valuation> builder = ImmutableList.builder();
        for (final VarIndexing indexing : indexings) {
            builder.add(PathUtils.extractValuation(model, indexing));
        }
        return ExprTraceStatus.feasible(Trace.of(builder.build(), trace.getActions()));
    }

    private ExprTraceStatus.Infeasible<ItpRefutation> createRefinement(
        final Collection<Expr<BoolType>> unsatCore,
        final List<VarIndexing> indexings,
        final Trace<? extends ExprState, ? extends ExprAction> trace
    ) {
        final int stateCount = trace.getStates().size();
        final List<Expr<BoolType>> wps = calculateWpStates(trace, indexings);

        final List<Expr<BoolType>> predicates = new ArrayList<>();
        final List<Expr<BoolType>> dataRegions = new ArrayList<>();

        for(var i = 0; i < stateCount; i++) {
            try (WithPushPop wpp = new WithPushPop(solver)) {
                /* Calculate SP */
                if (i == 0) {
                    dataRegions.addAll(ExprUtils.getConjuncts(PathUtils.unfold(init, indexings.get(i))));
                    solver.track(ExprUtils.getConjuncts(PathUtils.unfold(init, indexings.get(i))));

                    dataRegions.addAll(ExprUtils.getConjuncts(PathUtils.unfold(trace.getState(i).toExpr(), indexings.get(i))));
                    solver.track(ExprUtils.getConjuncts(PathUtils.unfold(trace.getState(i).toExpr(), indexings.get(i))));
                } else /* i > 0 */ {
                    dataRegions.addAll(ExprUtils.getConjuncts(predicates.get(i - 1)));
                    solver.track(ExprUtils.getConjuncts(predicates.get(i - 1)));

                    dataRegions.addAll(ExprUtils.getConjuncts(PathUtils.unfold(trace.getAction(i - 1).toExpr(), indexings.get(i - 1))));
                    solver.track(ExprUtils.getConjuncts(PathUtils.unfold(trace.getAction(i - 1).toExpr(), indexings.get(i - 1))));

                    if (i == stateCount - 1) {
                        dataRegions.addAll(ExprUtils.getConjuncts(PathUtils.unfold(target, indexings.get(i))));
                        solver.track(ExprUtils.getConjuncts(PathUtils.unfold(target, indexings.get(i))));
                    }
                }

                /* Add wp */
                solver.track(wps.get(i));

                solver.check();
                assert solver.check().isUnsat(); // It must be unsat
                Collection<Expr<BoolType>> uc = solver.getUnsatCore();

                /* Keep only those expressions from uc that are not in the data region */
                final Collection<Expr<BoolType>> predicate = new ArrayList<>();
                for (var ucExpr : uc) {
                    if (!dataRegions.contains(ucExpr)) {
                        predicate.add(ucExpr);
                    }
                }

                /* Add the negated of the above expression as the new predicate */
                predicates.add(
                    ExprSimplifier.simplify(
                        Not(And(new HashSet<>(predicate))),
                        ImmutableValuation.empty()
                    )
                );
            }
        }
        return ExprTraceStatus.infeasible(
            ItpRefutation.sequence(
                IntStream.range(0, predicates.size())
                    .mapToObj(i -> PathUtils.foldin(predicates.get(i), indexings.get(i)))
                    .collect(Collectors.toUnmodifiableList())
            )
        );
    }

    @SuppressWarnings("unchecked")
    private List<Expr<BoolType>> calculateWpStates(
            final Trace<? extends ExprState, ? extends ExprAction> trace,
            final List<VarIndexing> indexings
    ) {
        final int stateCount = trace.getStates().size();
        final List<Expr<BoolType>> wps = new ArrayList<>(Collections.nCopies(stateCount, null));

        final Trace<? extends ExprState, ? extends StmtAction> wptrace;
        try {
            wptrace = (Trace<? extends ExprState, ? extends StmtAction>) trace;
        }
        catch(ClassCastException e) {
            throw new UnsupportedOperationException("Actions must be of type StmtAction", e);
        }

        var wpstate = WpState.of(target);
        wps.set(stateCount - 1, target);
        for(var i = stateCount - 1; i > 0; i--) {
            var state = wptrace.getState(i);
            var action = wptrace.getAction(i - 1);

            for(var stmt : Lists.reverse(action.getStmts())) {
                wpstate = wpstate.wep(stmt);
            }

            wps.set(i - 1, PathUtils.unfold(wpstate.getExpr(), indexings.get(i - 1)));
        }

        return wps;
    }
}
