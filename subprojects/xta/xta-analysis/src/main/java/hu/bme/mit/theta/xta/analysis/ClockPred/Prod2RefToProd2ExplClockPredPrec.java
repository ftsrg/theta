package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.Prod2Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ZoneRefutation;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ClockPredPrec;
import hu.bme.mit.theta.analysis.zone.*;
import hu.bme.mit.theta.core.clock.constr.ClockConstr;
import hu.bme.mit.theta.core.clock.constr.DiffLeqConstr;
import hu.bme.mit.theta.core.clock.constr.DiffLtConstr;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.Collection;
import java.util.Iterator;

import static com.google.common.base.Preconditions.checkNotNull;

public class Prod2RefToProd2ExplClockPredPrec implements RefutationToPrec<Prod2Prec<ExplPrec, ClockPredPrec>, Prod2Refutation<ItpRefutation, ZoneRefutation>> {


    @Override
    public Prod2Prec<ExplPrec, ClockPredPrec> toPrec(Prod2Refutation<ItpRefutation, ZoneRefutation> refutation, int index) {
        ClockPredPrec clockPredPrec = ClockPredPrec.emptyPrec(refutation.getRefutation2().getClocks());
        ExplPrec explPrec = ExplPrec.empty();
        if(refutation.getRefutation2().getPruneIndex()>=0) {
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
        if(refutation.getRefutation1().getPruneIndex()>=0) {
            final Expr<BoolType> expr = refutation.getRefutation1().get(index);
            final Collection<VarDecl<?>> vars = ExprUtils.getVars(expr);
            explPrec = ExplPrec.of(vars);
        }
        return Prod2Prec.of(explPrec,clockPredPrec);


    }


    @Override
    public Prod2Prec<ExplPrec, ClockPredPrec> join(Prod2Prec<ExplPrec, ClockPredPrec> prec1, Prod2Prec<ExplPrec, ClockPredPrec> prec2) {
        checkNotNull(prec1.getPrec1());
        checkNotNull(prec2.getPrec1());
        return Prod2Prec.of(prec1.getPrec1().join(prec2.getPrec1()), prec1.getPrec2().join(prec2.getPrec2()) );
    }
}
