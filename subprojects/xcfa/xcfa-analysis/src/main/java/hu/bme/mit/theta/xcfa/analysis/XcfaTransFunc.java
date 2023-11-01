package hu.bme.mit.theta.xcfa.analysis;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.algorithm.AbstractMonolithicTransFunc;
import hu.bme.mit.theta.analysis.algorithm.MonolithicTransFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
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
import hu.bme.mit.theta.xcfa.UtilsKt;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class XcfaTransFunc extends AbstractMonolithicTransFunc {
    private XcfaTransFunc(XCFA xcfa){
            Preconditions.checkArgument(xcfa.getInitProcedures().size() == 1);
            var proc = xcfa.getInitProcedures().stream().findFirst().orElse(null).getFirst();
            assert proc != null;
            Preconditions.checkArgument(proc.getEdges().stream().map(UtilsKt::getFlatLabels).noneMatch(it -> it.stream().anyMatch(i -> !(i instanceof StmtLabel))));
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
            var transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0));
            transExpr = And(transUnfold.getExprs());
            initExpr = Eq(locVar.getRef(), Int(map.get(proc.getInitLoc())));
            firstIndex = VarIndexingFactory.indexing(0);
            offsetIndex = transUnfold.getIndexing();
            propExpr = Neq(locVar.getRef(), Int(map.get(proc.getErrorLoc().get())));
    }
    public static MonolithicTransFunc create(XCFA xcfa){
            return new XcfaTransFunc(xcfa);
    }
}
