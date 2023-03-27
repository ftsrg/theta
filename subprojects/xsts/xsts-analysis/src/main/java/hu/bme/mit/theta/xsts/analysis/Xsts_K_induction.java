package hu.bme.mit.theta.xsts.analysis;


import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expl.ExplOrd;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;


public class Xsts_K_induction {


    public SafetyResult<XstsState<ExplState>, XstsAction> check(XSTS xsts, int bound, Solver solver) {
        int i = 0;
        // Used as a placeholder for now for a real ARG just to be able to return a safety result
        ARG<XstsState<ExplState>, XstsAction> justAnArg = ARG.create(XstsOrd.create(ExplOrd.getInstance()));

        List<Stmt> atomicStep = new ArrayList<>();

        atomicStep.add(xsts.getEnv());
        atomicStep.add(xsts.getTran());

        var inductiveCurrStep = StmtUtils.toExpr(atomicStep, VarIndexingFactory.indexing(0));

        final var exprsFromStart = new ArrayList<Expr<BoolType>>();
        var init = StmtUtils.toExpr(xsts.getInit(), VarIndexingFactory.indexing(0));
        var currStep = StmtUtils.toExpr(atomicStep, init.getIndexing());
        exprsFromStart.add(xsts.getInitFormula());
        exprsFromStart.addAll(init.getExprs());
        exprsFromStart.addAll(currStep.getExprs());

        var listOfIndexes = new ArrayList<VarIndexing>();
        listOfIndexes.add(VarIndexingFactory.indexing(0));
        listOfIndexes.add(currStep.getIndexing());


        var exprsForInductivity = new ArrayList<>(inductiveCurrStep.getExprs());
        exprsForInductivity.add(xsts.getProp());

        ArrayList<XstsState<ExplState>> list = new ArrayList<>();
        ArrayList<XstsAction> actionList = new ArrayList<>();

        var varEqs = new ArrayList<Expr<BoolType>>();
        var varExpr = And(varEqs);
        while (i < bound) {
            if (i > 0) {
                exprsFromStart.addAll(StmtUtils.toExpr(atomicStep, currStep.getIndexing()).getExprs());
                var tempIndex= currStep.getIndexing();
                currStep = StmtUtils.toExpr(atomicStep, currStep.getIndexing());
                listOfIndexes.add(currStep.getIndexing());

                for(var v: xsts.getVars()){
                    varEqs.add(Eq(PathUtils.unfold(v.getRef(),tempIndex),PathUtils.unfold(v.getRef(),currStep.getIndexing())));

                }
                varExpr = Not(And(varEqs));

                exprsForInductivity.add(ExprUtils.applyPrimes(xsts.getProp(), inductiveCurrStep.getIndexing()));
                inductiveCurrStep = StmtUtils.toExpr(atomicStep, inductiveCurrStep.getIndexing());
                exprsForInductivity.addAll(inductiveCurrStep.getExprs());
            }

            // Checking loop free path of length i
            try (var s = new WithPushPop(solver)) {
                solver.add(PathUtils.unfold(And(exprsFromStart), 0));
                solver.add(varExpr);

                if(solver.check().isUnsat()){
                    return SafetyResult.safe(justAnArg);
                }
            }



            // Counterexample feasibility check
            try (var s = new WithPushPop(solver)) {
                // I1 and T1-2 and T2-3 and ... and Tk-1-k
                solver.add(PathUtils.unfold(And(exprsFromStart), 0));
                // Not Pk
                solver.add(PathUtils.unfold(Not(xsts.getProp()), currStep.getIndexing()));

                if (solver.check().isSat()) {
                    for (int j = 0; j < listOfIndexes.size(); j++) {
                        var valuation = PathUtils.extractValuation(solver.getModel(), listOfIndexes.get(j), xsts.getVars());
                        var el = XstsState.of(ExplState.of(valuation), false, true);
                        XstsAction concatAction = XstsAction.create(List.of(xsts.getEnv(), xsts.getTran()));
                        actionList.add(concatAction);
                        list.add(el);
                    }
                    actionList.remove(actionList.size() - 1);
                    var trace = Trace.of(list, actionList);
                    return SafetyResult.unsafe(trace, justAnArg);
                }
            }

            // Property k-inductivity check
            try (var s = new WithPushPop(solver)) {
                // P1 and T1-2 and P2 and ... and Tk-k+1
                solver.add(PathUtils.unfold(And(exprsForInductivity), VarIndexingFactory.indexing(0)));
                // Not Pk+1
                solver.add(PathUtils.unfold(Not(xsts.getProp()), inductiveCurrStep.getIndexing()));

                if (solver.check().isUnsat()) {
                    return SafetyResult.safe(justAnArg);
                }
            }
            i++;
        }

        //return SafetyResult.safe(justAnArg);
        throw new RuntimeException("unknown");

    }


}

