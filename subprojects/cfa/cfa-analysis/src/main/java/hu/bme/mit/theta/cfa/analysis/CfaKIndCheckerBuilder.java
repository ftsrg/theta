package hu.bme.mit.theta.cfa.analysis;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.algorithm.kind.KIndChecker;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class CfaKIndCheckerBuilder {

    public static KIndChecker<ExplState, StmtAction> create(CFA cfa, SolverFactory solverFactory, int maxBound) {
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
        final var trans = NonDetStmt.of(tranList);
        final var transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0));
        final var transExpr = And(transUnfold.getExprs());
        final var vars = ExprUtils.getVars(transExpr);

        final var initExpr = Eq(locVar.getRef(), Int(map.get(cfa.getInitLoc())));
        final var propExpr = Neq(locVar.getRef(), Int(map.get(cfa.getErrorLoc().get())));
        return new KIndChecker<>(transExpr, initExpr, propExpr, maxBound, solverFactory.createSolver(), VarIndexingFactory.indexing(0), transUnfold.getIndexing(), ExplState::of, vars);
    }

}
