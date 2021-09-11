package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.analysis.prec.GlobalXcfaPrec;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.Set;

public final class XcfaInitPrecs {

    private XcfaInitPrecs() {}

//    public static LocalXcfaPrec<PredPrec> collectAssumesLocal(XCFA xcfa) {
//        Map<XcfaLocation, PredPrec> precs = Containers.createMap();
//        for (XcfaProcess process : xcfa.getProcesses()) {
//            for (XcfaProcedure procedure : process.getProcedures()) {
//                for (XcfaLocation l : procedure.getLocs()) {
//                    Set<Expr<BoolType>> exprs = l.getIncomingEdges().stream().map(xcfaEdge -> xcfaEdge.getStmts().stream().filter(stmt -> stmt instanceof AssumeStmt).map(stmt -> ((AssumeStmt) stmt).getCond())).reduce(Streams::concat).orElse(Stream.empty()).collect(Collectors.toSet());
//                    precs.put(l, PredPrec.of(exprs));
//                }
//            }
//        }
//        return LocalXcfaPrec.create(precs, PredPrec.of());
//    }

    public static GlobalXcfaPrec<PredPrec> collectAssumesGlobal(XCFA xcfa) {
        Set<Expr<BoolType>> assumes = Containers.createSet();
        for (XcfaProcess process : xcfa.getProcesses()) {
            for (XcfaProcedure procedure : process.getProcedures()) {
                for (XcfaEdge edge : procedure.getEdges()) {
                    for (Stmt stmt : edge.getLabels()) {
                        if(stmt instanceof AssumeStmt) {
                            AssumeStmt assumeStmt = (AssumeStmt)stmt;
                            assumes.add(ExprUtils.ponate(assumeStmt.getCond()));
                        }
                    }
                }
            }
        }
        return GlobalXcfaPrec.create(PredPrec.of(assumes));
    }
}
