package hu.bme.mit.theta.xta.analysis.ClockPred;

import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.rattype.RatType;

import java.util.Collection;

public class ClockPredState implements ExprState {

    private final Collection<VarDecl<RatType>> clocks;

    //private final ZoneState zoneState;

    private ClockPredState(final Collection<VarDecl<RatType>> clocks){
        this.clocks = ImmutableSet.copyOf(clocks);

    }
    @Override
    public boolean isBottom() {
        return false;
    }

    @Override
    public Expr<BoolType> toExpr() {
        return null;
    }
    public boolean isLeq(ClockPredState state1){
        if(clocks.contains(state1.clocks) && clocks.size() >= state1.clocks.size()) return  true;
        return false;
    }
}
