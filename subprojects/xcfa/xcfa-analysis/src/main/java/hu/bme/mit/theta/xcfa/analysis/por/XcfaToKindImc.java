package hu.bme.mit.theta.xcfa.analysis.por;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.imc.ImcChecker;
import hu.bme.mit.theta.analysis.algorithm.kind.KIndChecker;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.StmtAction;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import org.checkerframework.checker.units.qual.K;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class XcfaToKindImc {
     Expr<BoolType> transExpr;
     Expr<BoolType> initExpr;
     Expr<BoolType> propExpr;
     int upperBound;
     SolverFactory solverFactory;
     Set<VarDecl<?>> vars;
     StmtUnfoldResult transUnfold;
    
     
    public XcfaToKindImc(XCFA xcfa,int bound,SolverFactory solverFactory) {
        Preconditions.checkArgument(xcfa.getProcedures().size() == 1);

        var proc = xcfa.getProcedures().stream().findFirst().orElse(null);
        Preconditions.checkArgument(proc.getErrorLoc().isPresent());
        int i=0;
        final Map<XcfaLocation,Integer> map = new HashMap<>();
        for(var x : proc.getLocs()){
            map.put(x,i++);
        }
        var locVar = Decls.Var("loc",Int());
        List<Stmt> tranList = proc.getEdges().stream().map(e-> SequenceStmt.of(List.of(
                AssumeStmt.of(Eq(locVar.getRef(),Int(map.get(e.getSource())))),
                e.getLabel().toStmt(),
                AssignStmt.of(locVar, Int(map.get(e.getTarget())))
        ))).collect(Collectors.toList());
        final var trans = NonDetStmt.of(tranList);
        transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0));
        transExpr = And(transUnfold.getExprs());
        vars = ExprUtils.getVars(transExpr);
        initExpr = Eq(locVar.getRef(), Int(map.get(proc.getInitLoc())));
        propExpr = Neq(locVar.getRef(), Int(map.get(proc.getErrorLoc().get())));
        upperBound = bound;

    }
    public  KIndChecker<ExplState, StmtAction> createKind() {
        return new KIndChecker<>(transExpr, initExpr, propExpr, upperBound, solverFactory.createSolver(), VarIndexingFactory.indexing(0), transUnfold.getIndexing(), ExplState::of, vars);
    }
    public  ImcChecker<ExplState, StmtAction> createImc() {
        return new ImcChecker<>(transExpr, initExpr, propExpr, upperBound, solverFactory.createItpSolver(), VarIndexingFactory.indexing(0), transUnfold.getIndexing(), ExplState::of, vars,true);
    }

}
