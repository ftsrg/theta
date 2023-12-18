package hu.bme.mit.theta.core.clock.impl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.clocktype.ClockType;
import hu.bme.mit.theta.core.type.rattype.RatType;

import java.util.Collection;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Add;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Sub;

public final class RatClockImpl extends ClockImpl<RatType> {

    protected RatClockImpl(final Collection<VarDecl<ClockType>> clocks) {
        super(clocks);
    }

    public static RatClockImpl fromClocks(final Collection<VarDecl<ClockType>> clocks) {
        return new RatClockImpl(clocks);
    }

    @Override
    protected RatType type() {
        return Rat();
    }

    @Override
    protected Expr<RatType> addExpr(Expr<RatType> leftOp, Expr<RatType> rightOp) {
        return Add(leftOp, rightOp);
    }

    @Override
    protected Expr<RatType> subExpr(Expr<RatType> leftOp, Expr<RatType> rightOp) {
        return Sub(leftOp, rightOp);
    }
}
