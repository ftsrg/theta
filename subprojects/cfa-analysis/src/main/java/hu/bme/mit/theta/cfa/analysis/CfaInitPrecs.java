package hu.bme.mit.theta.cfa.analysis;

import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec;
import hu.bme.mit.theta.cfa.analysis.prec.LocalCfaPrec;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public final class CfaInitPrecs {

    private CfaInitPrecs() {}

    public static LocalCfaPrec<PredPrec> collectAssumesLocal(CFA cfa) {
        Map<CFA.Loc, PredPrec> precs = new HashMap<>();
        for (CFA.Loc l : cfa.getLocs()) {
            Set<Expr<BoolType>> exprs = new HashSet<>();
            for (CFA.Edge e : l.getInEdges()) {
                CFA.Edge running = e;
                while (running != null) {
                    if (running.getStmt() instanceof AssumeStmt) {
                        AssumeStmt assumeStmt = (AssumeStmt) running.getStmt();
                        exprs.add(ExprUtils.ponate(assumeStmt.getCond()));
                    }
                    CFA.Loc source = running.getSource();
                    running = null;
                    if (source.getInEdges().size() == 1 && source.getOutEdges().size() == 1)
                        running = Utils.singleElementOf(source.getInEdges());
                }
            }
            precs.put(l, PredPrec.of(exprs));
        }
        return LocalCfaPrec.create(precs, PredPrec.of());
    }

    public static GlobalCfaPrec<PredPrec> collectAssumesGlobal(CFA cfa) {
        Set<Expr<BoolType>> assumes = new HashSet<>();
        for (CFA.Edge e : cfa.getEdges()) {
            if (e.getStmt() instanceof AssumeStmt) {
                AssumeStmt assumeStmt = (AssumeStmt)e.getStmt();
                assumes.add(ExprUtils.ponate(assumeStmt.getCond()));
            }
        }
        return GlobalCfaPrec.create(PredPrec.of(assumes));
    }
}
