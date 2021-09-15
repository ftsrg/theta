package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public class Prod2ExplPredAbstractors {

    private Prod2ExplPredAbstractors() {}

    public interface Prod2ExplPredAbstractor {

        Collection<Prod2State<ExplState, PredState>> createStatesForExpr(final Expr<BoolType> expr, final VarIndexing exprIndexing,
                                                                         final Prod2Prec<ExplPrec,PredPrec> prec, final VarIndexing precIndexing,
                                                                         final Function<? super Valuation, ? extends ExplState> valuationToState, final int limit);

    }

    public static BooleanAbstractor booleanAbstractor(final Solver solver){
        return new BooleanAbstractor(solver, false);
    }

    private static final class BooleanAbstractor implements Prod2ExplPredAbstractor{

        private final Solver solver;
        private final List<ConstDecl<BoolType>> actLits;
        private final String litPrefix;
        private static int instanceCounter = 0;
        private final boolean split;

        public BooleanAbstractor(final Solver solver, final boolean split) {
            this.solver = checkNotNull(solver);
            this.actLits = new ArrayList<>();
            this.litPrefix = "__Prod2ExplPred" + getClass().getSimpleName() + "_" + instanceCounter + "_";
            instanceCounter++;
            this.split = split;
        }

        @Override
        public Collection<Prod2State<ExplState, PredState>> createStatesForExpr(final Expr<BoolType> expr, final VarIndexing exprIndexing,
                                                                                final Prod2Prec<ExplPrec, PredPrec> prec, final VarIndexing stateIndexing,
                                                                                final Function<? super Valuation, ? extends ExplState> valuationToState, final int limit) {
            checkNotNull(expr);
            checkNotNull(exprIndexing);
            checkNotNull(prec);
            checkNotNull(stateIndexing);

            final List<Expr<BoolType>> preds = new ArrayList<>(prec.getPrec2().getPreds());
            generateActivationLiterals(preds.size());

            assert actLits.size() >= preds.size();

            final List<Prod2State<ExplState,PredState>> states = new LinkedList<>();
            try (WithPushPop wp = new WithPushPop(solver)) {
                solver.add(PathUtils.unfold(expr, exprIndexing));
                for (int i = 0; i < preds.size(); ++i) {
                    solver.add(Iff(actLits.get(i).getRef(), PathUtils.unfold(preds.get(i), stateIndexing)));
                }
                while (solver.check().isSat() && (limit == 0 || states.size() < limit)) {
                    final Valuation model = solver.getModel();

                    final Valuation valuation = PathUtils.extractValuation(model, stateIndexing);
                    final ExplState explState = valuationToState.apply(valuation);

                    final Set<Expr<BoolType>> newStatePreds = Containers.createSet();
                    final List<Expr<BoolType>> feedback = new LinkedList<>();
                    feedback.add(True());
                    for (int i = 0; i < preds.size(); ++i) {
                        final ConstDecl<BoolType> lit = actLits.get(i);
                        final Expr<BoolType> pred = preds.get(i);
                        final Optional<LitExpr<BoolType>> eval = model.eval(lit);
                        if (eval.isPresent()) {
                            if (eval.get().equals(True())) {
                                newStatePreds.add(pred);
                                feedback.add(lit.getRef());
                            } else {
                                newStatePreds.add(prec.getPrec2().negate(pred));
                                feedback.add(Not(lit.getRef()));
                            }
                        }
                    }
                    final Set<Expr<BoolType>> simplfiedNewStatePreds = newStatePreds.stream().map(pred -> ExprUtils.simplify(pred,explState)).collect(Collectors.toSet());
                    final PredState predState = PredState.of(simplfiedNewStatePreds);

                    final Prod2State<ExplState,PredState> prod2ExplPredState = Prod2State.of(explState,predState);
                    states.add(prod2ExplPredState);
                    solver.add(Not(And(PathUtils.unfold(explState.toExpr(), stateIndexing),And(feedback))));
                }

            }
            return states;
        }

        private void generateActivationLiterals(final int n) {
            while (actLits.size() < n) {
                actLits.add(Decls.Const(litPrefix + actLits.size(), BoolExprs.Bool()));
            }
        }
    }

}
