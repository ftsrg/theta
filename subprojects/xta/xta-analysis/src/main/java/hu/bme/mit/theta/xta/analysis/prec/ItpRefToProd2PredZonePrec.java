package hu.bme.mit.theta.xta.analysis.prec;

import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.pred.ExprSplitters;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public class ItpRefToProd2PredZonePrec implements RefutationToPrec<Prod2Prec<PredPrec, ZonePrec>, ItpRefutation> {
    private final ExprSplitters.ExprSplitter exprSplitter;
    private final ZonePrec zonePrec;

    private ItpRefToProd2PredZonePrec(final ExprSplitters.ExprSplitter _splitter, ZonePrec _zonePrec){
        exprSplitter = checkNotNull(_splitter);
        zonePrec = checkNotNull(_zonePrec);
    }

    public static ItpRefToProd2PredZonePrec create(final ExprSplitters.ExprSplitter exprSplitter,  ZonePrec _zonePrec) {

        return new ItpRefToProd2PredZonePrec(exprSplitter, _zonePrec);
    }

    @Override
    public Prod2Prec<PredPrec, ZonePrec> toPrec(ItpRefutation refutation, int index) {
        final Expr<BoolType> refExpr = refutation.get(index);

        final var predSelectedExprs = exprSplitter.apply(refExpr).stream()
                .collect(Collectors.toSet());
        return Prod2Prec.of(PredPrec.of(predSelectedExprs), ZonePrec.of(Collections.emptyList()));
    }

    @Override
    public Prod2Prec<PredPrec, ZonePrec> join(Prod2Prec<PredPrec, ZonePrec> prec1, Prod2Prec<PredPrec, ZonePrec> prec2) {
        final PredPrec joinedPred = prec1.getPrec1().join(prec2.getPrec1());

        final var filteredPreds = joinedPred.getPreds().stream()
                .collect(Collectors.toList());
        final PredPrec filteredPred = PredPrec.of(filteredPreds);
        return Prod2Prec.of(filteredPred, ZonePrec.of(Collections.emptyList()));
    }
}