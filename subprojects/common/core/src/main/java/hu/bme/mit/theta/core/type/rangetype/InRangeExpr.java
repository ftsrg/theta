package hu.bme.mit.theta.core.type.rangetype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;

public class InRangeExpr extends UnaryExpr<IntType, BoolType> {

    private static final int HASH_SEED = 4538;

    private final RangeType range;

    private InRangeExpr(final Expr<IntType> op, final RangeType range) {
        super(op);
        this.range = range;
    }

    public static InRangeExpr of(final Expr<IntType> op, final RangeType range) {
        return new InRangeExpr(op, range);
    }

    @Override
    public UnaryExpr<IntType, BoolType> with(final Expr<IntType> op) {
        return InRangeExpr.of(op, range);
    }

    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public LitExpr<BoolType> eval(final Valuation val) {
        final IntLitExpr litExpr = (IntLitExpr) getOp().eval(val);
        final int value = litExpr.getValue().intValue();
        return Bool(range.getLower() <= value && value <= range.getUpper());
    }

    public RangeType getRange() {
        return range;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof InRangeExpr) {
            final InRangeExpr that = (InRangeExpr) obj;
            return this.getOp().equals(that.getOp());
        } else {
            return false;
        }
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public String getOperatorLabel() {
        return "in " + range;
    }
}
