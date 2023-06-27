package hu.bme.mit.theta.core.type.clocktype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.AsymBinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public abstract class ClockConstraintExpr extends AsymBinaryExpr<ClockType, IntType, BoolType> {

    private static final int HASH_SEED = 81673;

    public enum ClockConstraintRel {
        LT, LEQ, GT, GEQ, EQ
    }

    protected ClockConstraintExpr(final Expr<ClockType> clock, final Expr<IntType> value) {
        super(clock, value);
    }

    public abstract ClockConstraintRel getRel();

    @Override
    public AsymBinaryExpr<ClockType, IntType, BoolType> withLeftOp(Expr<ClockType> clock) {
        return with(clock, getRightOp());
    }

    @Override
    public AsymBinaryExpr<ClockType, IntType, BoolType> withRightOp(Expr<IntType> value) {
        return with(getLeftOp(), value);
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }


    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public LitExpr<BoolType> eval(Valuation val) {
        throw new UnsupportedOperationException();
    }
}
