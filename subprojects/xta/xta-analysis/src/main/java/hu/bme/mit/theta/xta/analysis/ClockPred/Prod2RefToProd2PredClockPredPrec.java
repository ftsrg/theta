package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.Prod2Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ZoneRefutation;
import hu.bme.mit.theta.analysis.pred.ExprSplitters;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ClockPredPrec;
import hu.bme.mit.theta.analysis.zone.DiffBounds;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.clock.constr.ClockConstr;
import hu.bme.mit.theta.core.clock.constr.DiffLeqConstr;
import hu.bme.mit.theta.core.clock.constr.DiffLtConstr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Collections;
import java.util.Iterator;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public class Prod2RefToProd2PredClockPredPrec implements RefutationToPrec<Prod2Prec<PredPrec, ClockPredPrec>, Prod2Refutation<ItpRefutation, ZoneRefutation>> {

    private final ExprSplitters.ExprSplitter exprSplitter;

    public Prod2RefToProd2PredClockPredPrec(final ExprSplitters.ExprSplitter _splitter){
        exprSplitter = checkNotNull(_splitter);
    }
    @Override
    public Prod2Prec<PredPrec, ClockPredPrec> toPrec(Prod2Refutation<ItpRefutation, ZoneRefutation> refutation, int index) {
        ClockPredPrec clockPredPrec = ClockPredPrec.emptyPrec(refutation.getRefutation2().getClocks());
        PredPrec predPrec = PredPrec.of();
        if(refutation.getRefutation2().getPruneIndex() >= 0) {
            final ZoneState zone = refutation.getRefutation2().get(index);
            if (!(zone.isBottom() || zone.isTop())) {
                Iterator<ClockConstr> iterator = zone.getDbm().getConstrs().iterator();
                while (iterator.hasNext()) {
                    ClockConstr constr = iterator.next();

                    if (constr instanceof DiffLtConstr ltconstr) {
                        clockPredPrec.add(ltconstr.getLeftVar(), ltconstr.getRightVar(), DiffBounds.Lt(ltconstr.getBound()));
                    } else if (constr instanceof DiffLeqConstr leqconstr) {
                        clockPredPrec.add(leqconstr.getLeftVar(), leqconstr.getRightVar(), DiffBounds.Leq(leqconstr.getBound()));
                    }
                }
            }
        }
        if(refutation.getRefutation1().getPruneIndex() >= 0) {
            final Expr<BoolType> refExpr = refutation.getRefutation1().get(index);

            final var predSelectedExprs = exprSplitter.apply(refExpr).stream()
                    .collect(Collectors.toSet());
            predPrec = PredPrec.of(predSelectedExprs);
        }
            return Prod2Prec.of(predPrec, clockPredPrec);


    }

    @Override
    public Prod2Prec<PredPrec, ClockPredPrec> join(Prod2Prec<PredPrec, ClockPredPrec> prec1, Prod2Prec<PredPrec, ClockPredPrec> prec2) {
        return (Prod2Prec<PredPrec, ClockPredPrec>)prec1.join(prec2);
    }
}