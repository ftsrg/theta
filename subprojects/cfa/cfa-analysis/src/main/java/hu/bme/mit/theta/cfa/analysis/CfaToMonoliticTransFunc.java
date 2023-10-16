package hu.bme.mit.theta.cfa.analysis;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.algorithm.AbstractMonolithicTransFunc;
import hu.bme.mit.theta.analysis.algorithm.MonolithicTransFunc;
import hu.bme.mit.theta.analysis.algorithm.kind.KIndChecker;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class CfaToMonoliticTransFunc extends AbstractMonolithicTransFunc {
    private CfaToMonoliticTransFunc(CFA cfa) {
        Preconditions.checkArgument(cfa.getErrorLoc().isPresent());

        int i = 0;
        final Map<CFA.Loc, Integer> map = new HashMap<>();
        for (var x : cfa.getLocs()) {
            map.put(x, i++);
        }
        var locVar = Decls.Var("loc", Int());
        List<Stmt> tranList = cfa.getEdges().stream().map(e -> SequenceStmt.of(List.of(
                AssumeStmt.of(Eq(locVar.getRef(), Int(map.get(e.getSource())))),
                e.getStmt(),
                AssignStmt.of(locVar, Int(map.get(e.getTarget())))
        ))).collect(Collectors.toList());
        var trans = NonDetStmt.of(tranList);
        var transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0));
        transExpr = And(transUnfold.getExprs());
        initExpr = Eq(locVar.getRef(), Int(map.get(cfa.getInitLoc())));
        propExpr = Neq(locVar.getRef(), Int(map.get(cfa.getErrorLoc().get())));

        firstIndex = VarIndexingFactory.indexing(0);
        offsetIndex = transUnfold.getIndexing();
    }

    public static MonolithicTransFunc create(CFA cfa) {
        return new CfaToMonoliticTransFunc(cfa);
    }
}
