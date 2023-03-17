package hu.bme.mit.theta.xsts.analysis;


import com.google.errorprone.annotations.Var;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expl.ExplOrd;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import hu.bme.mit.theta.xsts.XSTS;
import sun.misc.Unsafe;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

public class Xsts_K_induction {


    public SafetyResult<XstsState<ExplState>, XstsAction> check(XSTS xsts, int bound, Solver solver) {
        int i = 0;
        ARG<XstsState<ExplState>, XstsAction> justAnArg = ARG.create(XstsOrd.create(ExplOrd.getInstance()));

        List<Stmt> stmts = new ArrayList<>();

        stmts.add(xsts.getEnv());
        stmts.add(xsts.getTran());
        var init = StmtUtils.toExpr(xsts.getInit(), VarIndexingFactory.indexing(0));

        var unfoldResult = StmtUtils.toExpr(stmts, init.getIndexing());
        var unfoldResult2 = StmtUtils.toExpr(stmts, VarIndexingFactory.indexing(0));

        final var exprsFromStart = new ArrayList<Expr<BoolType>>();
        exprsFromStart.add(xsts.getInitFormula());
        exprsFromStart.addAll(init.getExprs());
        exprsFromStart.addAll(unfoldResult.getExprs());

        var exprsForInductivity = new ArrayList<>(unfoldResult.getExprs());
        var temp = unfoldResult;
        exprsForInductivity.add(xsts.getProp());
        var listOfIndexes = new ArrayList<VarIndexing>();
        listOfIndexes.add(VarIndexingFactory.indexing(0));
        listOfIndexes.add(unfoldResult.getIndexing());

        ArrayList<XstsState<ExplState>> list = new ArrayList<>();
        ArrayList<XstsAction> actionList = new ArrayList<>();

        while (i < bound) {
            if (i > 0) {
                exprsFromStart.addAll(StmtUtils.toExpr(stmts, unfoldResult.getIndexing()).getExprs());
                temp = unfoldResult;
                unfoldResult = StmtUtils.toExpr(stmts, unfoldResult.getIndexing());
                listOfIndexes.add(unfoldResult.getIndexing());

                exprsForInductivity.addAll(StmtUtils.toExpr(stmts, unfoldResult2.getIndexing()).getExprs());
                exprsForInductivity.add(ExprUtils.applyPrimes(xsts.getProp(), unfoldResult2.getIndexing()));
                unfoldResult2 = StmtUtils.toExpr(stmts, unfoldResult2.getIndexing());
            }


            exprsFromStart.add(ExprUtils.applyPrimes(Not(xsts.getProp()), temp.getIndexing()));

            try (var s = new WithPushPop(solver)) {
                solver.add(PathUtils.unfold(And(exprsFromStart), 0));

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
                exprsFromStart.remove(exprsFromStart.size()-1);
            }
            try (var s = new WithPushPop(solver)) {
                exprsForInductivity.addAll(StmtUtils.toExpr(stmts, unfoldResult.getIndexing()).getExprs());
                exprsForInductivity.add(ExprUtils.applyPrimes(xsts.getProp(), unfoldResult2.getIndexing()));

                solver.add(PathUtils.unfold(And(exprsForInductivity), VarIndexingFactory.indexing(0)));
                if (solver.check().isUnsat()) return SafetyResult.safe(justAnArg);
            }
            i++;
        }

        //return SafetyResult.safe(justAnArg);
        throw new RuntimeException("unknown");

    }
}

