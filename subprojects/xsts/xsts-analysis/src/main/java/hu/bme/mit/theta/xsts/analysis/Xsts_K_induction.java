package hu.bme.mit.theta.xsts.analysis;


import com.google.errorprone.annotations.Var;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
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

        List<Stmt> stmts = new ArrayList<>();

        stmts.add(xsts.getTran());
        stmts.add(xsts.getEnv());
        var exp= StmtUtils.toExpr(xsts.getInit(),VarIndexingFactory.indexing(0));


        var states= new ArrayList<Expr<BoolType>>();

        var unfoldResult =
                StmtUtils.toExpr(stmts, exp.getIndexing());
        var unfoldResult2 = StmtUtils.toExpr(stmts, exp.getIndexing());
        var exprs =new ArrayList<>(exp.getExprs());
        exprs.add(xsts.getInitFormula());

        var init =StmtUtils.toExpr(xsts.getInit(),VarIndexingFactory.indexing(0));
        exprs.addAll(init.getExprs());
        exprs.addAll(unfoldResult.getExprs());
        var exprs2 = new ArrayList<Expr<BoolType>>(unfoldResult2.getExprs());
        var temp= unfoldResult;
        exprs2.add(xsts.getProp());
        var listOfIndexes = new ArrayList<VarIndexing>();
        listOfIndexes.add(VarIndexingFactory.indexing(0));
        listOfIndexes.add(unfoldResult.getIndexing());

        ArrayList<XstsState<ExplState>> list =new ArrayList<>();
        ArrayList<XstsAction> actionList=new ArrayList<>();

        while (i < bound) {
            if (i > 0) {
                exprs.addAll(StmtUtils.toExpr(stmts, unfoldResult.getIndexing()).getExprs());
                temp= unfoldResult;
                unfoldResult = StmtUtils.toExpr(stmts, unfoldResult.getIndexing());
                listOfIndexes.add(unfoldResult.getIndexing());

                exprs2.addAll(StmtUtils.toExpr(stmts,unfoldResult2.getIndexing()).getExprs());
                exprs2.add(ExprUtils.applyPrimes(xsts.getProp(),unfoldResult2.getIndexing()));
                unfoldResult2=StmtUtils.toExpr(stmts,unfoldResult2.getIndexing());





            }

            exprs.add(xsts.getInitFormula());
            exprs.add(ExprUtils.applyPrimes(xsts.getProp(),temp.getIndexing()));

            try (var s = new WithPushPop(solver)) {
                solver.add(PathUtils.unfold(And(exprs), 0));

                if (solver.check().isSat()) {

                    for(int j=0;j<listOfIndexes.size();j++){
                        var valuation=PathUtils.extractValuation(solver.getModel(),listOfIndexes.get(j),xsts.getVars());
                        var el=XstsState.of(ExplState.of(valuation),false,true);
                        XstsAction concatAction=XstsAction.create(List.of(xsts.getEnv(),xsts.getTran()));
                        actionList.add(concatAction);
                        list.add(el);
                    }
                    actionList.remove(actionList.size()-1);
                    var trace= Trace.of(list,actionList);
                    return SafetyResult.unsafe(trace,null);
                }

            }
            try (var s = new WithPushPop(solver)) {
                exprs2.addAll(StmtUtils.toExpr(stmts, unfoldResult.getIndexing()).getExprs());
                exprs2.add(ExprUtils.applyPrimes(xsts.getProp(),unfoldResult2.getIndexing()));

                solver.add(PathUtils.unfold(And(exprs2), VarIndexingFactory.indexing(0)));
                if(solver.check().isUnsat()) return SafetyResult.safe(null);


            }
            i++;
        }

        throw new RuntimeException("unknown");

    }
}

