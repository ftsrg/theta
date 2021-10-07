package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.StmtApplier;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.pred.PredAbstractors;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredAbstractors.Prod2ExplPredAbstractor;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;

import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static java.util.Collections.singleton;

public class Prod2ExplPredDedicatedStmtTransFunc<A extends ExprAction> implements TransFunc<Prod2State<ExplState, PredState>, StmtAction, Prod2Prec<ExplPrec, PredPrec>> {

    private final Prod2ExplPredAbstractor prod2ExplPredAbstractor;

    private final Solver solver;
    // 0 means arbitrarily many
    private final int maxSuccToEnumerate;

    private Prod2ExplPredDedicatedStmtTransFunc(final Prod2ExplPredAbstractor prod2ExplPredAbstractor,
                                                final Solver solver,
                                                int maxSuccToEnumerate){
        this.prod2ExplPredAbstractor = prod2ExplPredAbstractor;
        this.solver = solver;
        this.maxSuccToEnumerate = maxSuccToEnumerate;
    }

    public static <A extends ExprAction> Prod2ExplPredDedicatedStmtTransFunc<A> create(final Prod2ExplPredAbstractor prod2ExplPredAbstractor,
                                                                                       final Solver solver,
                                                                                       int maxSuccToEnumerate){
        return new Prod2ExplPredDedicatedStmtTransFunc<A>(prod2ExplPredAbstractor, solver, maxSuccToEnumerate);
    }

    @Override
    public Collection<? extends Prod2State<ExplState, PredState>> getSuccStates(Prod2State<ExplState, PredState> state,
                                                                                StmtAction action, Prod2Prec<ExplPrec, PredPrec> prec) {
        checkNotNull(state);
        checkNotNull(action);
        checkNotNull(prec);

        return getSuccStates(state, action.getStmts(), prec);
    }

    Collection<Prod2State<ExplState, PredState>> getSuccStates(Prod2State<ExplState, PredState> state, final List<Stmt> stmts, final Prod2Prec<ExplPrec, PredPrec> prec) {
        final MutableValuation preciseVal = MutableValuation.copyOf(state.getState1());
        final StmtApplier.ApplyResult applyResult = StmtApplier.apply(SequenceStmt.of(stmts), preciseVal, false);

        final StmtUnfoldResult toExprResult = StmtUtils.toExpr(stmts, VarIndexingFactory.indexing(0));
        final Expr<BoolType> expr = And(state.toExpr(), And(toExprResult.getExprs()));
        final VarIndexing nextIdx = toExprResult.getIndexing();

        Valuation val = null;
        if (applyResult == StmtApplier.ApplyResult.SUCCESS){
            val = preciseVal;
        } else if (applyResult == StmtApplier.ApplyResult.BOTTOM) {
            return singleton(Prod2State.bottom1(ExplState.bottom()));
        } else if (applyResult == StmtApplier.ApplyResult.FAILURE) {
            // We query (max + 1) states from the solver to see if there
            // would be more than max
            final int maxToQuery = maxSuccToEnumerate == 0 ? 0 : maxSuccToEnumerate + 1;
            final Collection<Prod2State<ExplState,PredState>> succStates = prod2ExplPredAbstractor.createStatesForExpr(
                    expr, VarIndexingFactory.indexing(0), prec, nextIdx, prec.getPrec1()::createState, maxToQuery);

            if (succStates.isEmpty()) {
                return singleton(Prod2State.bottom1(ExplState.bottom()));
            } else if (maxSuccToEnumerate == 0 || succStates.size() <= maxSuccToEnumerate) {
                return succStates;
            } else {
                final MutableValuation approxVal = MutableValuation.copyOf(state.getState1());
                final StmtApplier.ApplyResult reapplyResult = StmtApplier.apply(SequenceStmt.of(stmts), approxVal, true);
                assert reapplyResult == StmtApplier.ApplyResult.SUCCESS;

                val = approxVal;
            }
        }

        checkNotNull(val);
        final ExplState explState = prec.getPrec1().createState(val);
        final Expr<BoolType> explExpr = ExprUtils.applyPrimes(explState.toExpr(), nextIdx);
        final Expr<BoolType> extendedExpr = And(expr, explExpr);

        final Collection<PredState> predStates = PredAbstractors.cartesianAbstractor(solver).createStatesForExpr(extendedExpr, VarIndexingFactory.indexing(0), prec.getPrec2(), nextIdx);
        if(predStates.size()==0) return singleton(Prod2State.bottom2(PredState.bottom()));
        assert predStates.size()==1 : "Cartesian abstraction returned more than one state";

        final PredState predState = predStates.iterator().next();
        return singleton(Prod2State.of(explState,predState));
    }
}
