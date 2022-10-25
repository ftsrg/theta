package hu.bme.mit.theta.xta.analysis.prec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.Collection;
import java.util.Collections;

import static com.google.common.base.Preconditions.checkNotNull;

public class ItpRefToProd2ExplZonePrec implements RefutationToPrec<Prod2Prec<ExplPrec, ZonePrec>, ItpRefutation> {
    @Override
    public Prod2Prec<ExplPrec, ZonePrec> toPrec(ItpRefutation refutation, int index) {
        final Expr<BoolType> expr = refutation.get(index);
        final Collection<VarDecl<?>> vars = ExprUtils.getVars(expr);
        final ExplPrec prec = ExplPrec.of(vars);
        return Prod2Prec.of(prec, ZonePrec.of(Collections.emptyList()));
    }

    @Override
    public Prod2Prec<ExplPrec, ZonePrec> join(Prod2Prec<ExplPrec, ZonePrec> prec1, Prod2Prec<ExplPrec, ZonePrec> prec2) {
        checkNotNull(prec1.getPrec1());
        checkNotNull(prec2.getPrec1());
        return Prod2Prec.of((ExplPrec)prec1.getPrec1().join(prec2.getPrec1()), ZonePrec.of(Collections.emptyList()));
    }
}
