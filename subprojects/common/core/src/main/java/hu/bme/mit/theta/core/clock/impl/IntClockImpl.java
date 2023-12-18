package hu.bme.mit.theta.core.clock.impl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.clocktype.ClockType;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.util.Collection;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;

public final class IntClockImpl extends ClockImpl<IntType> {

    protected IntClockImpl(final Collection<VarDecl<ClockType>> clocks) {
        super(clocks);
    }

    public static IntClockImpl fromClocks(final Collection<VarDecl<ClockType>> clocks) {
        return new IntClockImpl(clocks);
    }

    @Override
    protected IntType type() {
        return Int();
    }

    @Override
    protected Expr<IntType> addExpr(Expr<IntType> leftOp, Expr<IntType> rightOp) {
        return Add(leftOp, rightOp);
    }

    @Override
    protected Expr<IntType> subExpr(Expr<IntType> leftOp, Expr<IntType> rightOp) {
        return Sub(leftOp, rightOp);
    }
}
