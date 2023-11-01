package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.algorithm.AbstractMonolithicTransFunc;
import hu.bme.mit.theta.analysis.algorithm.MonolithicTransFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

public class XstsToMonoliticTransFunc extends AbstractMonolithicTransFunc {
    private XstsToMonoliticTransFunc(XSTS xsts){
        final StmtUnfoldResult initUnfoldResult = StmtUtils.toExpr(xsts.getInit(), VarIndexingFactory.indexing(0));
        initExpr  = And(And(initUnfoldResult.getExprs()), xsts.getInitFormula());
        firstIndex = initUnfoldResult.getIndexing();
        final var envTran = Stmts.SequenceStmt(List.of(xsts.getEnv(), xsts.getTran()));
        final StmtUnfoldResult envTranUnfoldResult = StmtUtils.toExpr(envTran, VarIndexingFactory.indexing(0));
        transExpr = And(envTranUnfoldResult.getExprs());
        offsetIndex = envTranUnfoldResult.getIndexing();
        propExpr = xsts.getProp();

    }
    public static MonolithicTransFunc create(XSTS xsts){
        return new XstsToMonoliticTransFunc(xsts);
    }
}
