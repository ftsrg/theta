package hu.bme.mit.theta.analysis.prod2.prod2explpred.mixed;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.StmtApplier;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.singleton;

public class MixedTransFunc<A extends StmtAction> implements TransFunc<Prod2State<ExplState, PredState>, A, Prod2Prec<ExplPrec, PredPrec>> {

    private final Solver solver;

    private MixedTransFunc(final Solver solver) {
        this.solver = solver;
    }

    public static <A extends StmtAction> MixedTransFunc<A> create(final Solver solver) {
        return new MixedTransFunc<A>(solver);
    }

    @Override
    public Collection<? extends Prod2State<ExplState, PredState>> getSuccStates(Prod2State<ExplState, PredState> state,
                                                                                A action, Prod2Prec<ExplPrec, PredPrec> prec) {
        checkNotNull(state);
        checkNotNull(action);
        checkNotNull(prec);

        checkArgument(action.getStmts().size() == 1, "Only implemented for a single stmt per action");
        final Stmt stmt = action.getStmts().get(0);

        // 1.: Best-effort statement applying
        final MutableValuation val = MutableValuation.copyOf(state.getState1());
        final StmtApplier.ApplyResult applyResult = StmtApplier.apply(stmt, val, true);

        if (applyResult == StmtApplier.ApplyResult.BOTTOM) {
            return singleton(Prod2State.of(ExplState.bottom(), PredState.bottom()));
        } else {
            // TODO make more efficient
            final Map<VarDecl<?>, Integer> predCounts = Containers.createMap();
            prec.getPrec2().getPreds().forEach(
                    pred -> ExprUtils.getVars(pred).forEach(
                            decl -> predCounts.put(decl, predCounts.getOrDefault(decl, 0) + 1)
                    )
            );

            final Set<VarDecl<?>> remainingVars = prec.getPrec1().getVars().stream()
                    .filter(Predicate.not(val.getDecls()::contains))
                    .collect(Collectors.toSet());

            final List<VarDecl<?>> remainingVarsOrdered =  remainingVars.stream()
                    .sorted(Comparator.comparingInt(predCounts::get))
                    .collect(Collectors.toList());


        }
        return null;
    }

}
