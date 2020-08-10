package hu.bme.mit.theta.cfa.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.HashSet;
import java.util.Set;

/**
 * An implementation for initial precision that returns all assumptions. Only
 * applicable for {@link PredPrec}.
 */
public class CfaAllAssumesInitPrec implements CfaInitPrec {

    @Override
    public ExplPrec createExpl(CFA cfa) {
        throw new UnsupportedOperationException("Initial precision not supported for this kind of precision");
    }

    @Override
    public PredPrec createPred(CFA cfa) {
        Set<Expr<BoolType>> assumes = new HashSet<>();
        for (CFA.Edge e : cfa.getEdges()) {
            if (e.getStmt() instanceof AssumeStmt) {
                AssumeStmt assumeStmt = (AssumeStmt)e.getStmt();
                Expr<BoolType> cond = assumeStmt.getCond();
                assumes.add(ExprUtils.ponate(cond));
            }
        }

        return PredPrec.of(assumes);
    }
}
