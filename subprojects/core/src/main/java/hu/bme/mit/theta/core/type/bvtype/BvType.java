package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.*;
import hu.bme.mit.theta.core.type.inttype.IntType;

import static com.google.common.base.Preconditions.checkArgument;

public final class BvType implements Additive<BvType>, Multiplicative<BvType>, Divisible<BvType>, Equational<BvType>, Ordered<BvType>, Castable<BvType> {
    private final static int HASH_SEED = 5674;
    private final static String TYPE_LABEL = "Bv";

    private final int size;
    private final boolean isSigned;

    private volatile int hashCode = 0;

    private BvType(final int size, final boolean isSigned) {
        checkArgument(size > 0);
        this.size = size;
        this.isSigned = isSigned;
    }

    public static BvType of(final int size, final boolean isSigned) {
        return new BvType(size, isSigned);
    }

    public int getSize() {
        return size;
    }

    public boolean isSigned() {
        return isSigned;
    }

    @Override
    public BvAddExpr Add(Iterable<? extends Expr<BvType>> ops) {
        return BvExprs.Add(ops);
    }

    @Override
    public BvSubExpr Sub(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvExprs.Sub(leftOp, rightOp);
    }

    @Override
    public BvPosExpr Pos(Expr<BvType> op) {
        return BvExprs.Pos(op);
    }

    @Override
    public BvNegExpr Neg(Expr<BvType> op) {
        return BvExprs.Neg(op);
    }

    @Override
    public BvMulExpr Mul(final Iterable<? extends Expr<BvType>> ops) {
        return BvExprs.Mul(ops);
    }

    @Override
    public BvDivExpr Div(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvExprs.Div(leftOp, rightOp);
    }


    @Override
    public ModExpr<BvType> Mod(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvExprs.Mod(leftOp, rightOp);
    }

    @Override
    public RemExpr<BvType> Rem(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvExprs.Rem(leftOp, rightOp);
    }

    @Override
    public EqExpr<BvType> Eq(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvEqExpr.of(leftOp, rightOp);
    }

    @Override
    public NeqExpr<BvType> Neq(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvNeqExpr.of(leftOp, rightOp);
    }

    @Override
    public LtExpr<BvType> Lt(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvLtExpr.of(leftOp, rightOp);
    }

    @Override
    public LeqExpr<BvType> Leq(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvLeqExpr.of(leftOp, rightOp);
    }

    @Override
    public GtExpr<BvType> Gt(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvGtExpr.of(leftOp, rightOp);
    }

    @Override
    public GeqExpr<BvType> Geq(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvGeqExpr.of(leftOp, rightOp);
    }

    @SuppressWarnings("unchecked")
    @Override
    public <TargetType extends Type> Expr<TargetType> Cast(final Expr<BvType> op, final TargetType type) {
        if (type instanceof IntType) {
            return (Expr<TargetType>) BvExprs.ToInt(op);
        } else {
            throw new ClassCastException("Bitvector cannot be cast to " + type);
        }
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + (isSigned ? 1 : 0);
            result = 31 * result + size;
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof BvType) {
            final BvType that = (BvType) obj;
            return this.getSize() == that.getSize() && this.isSigned() == that.isSigned();
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(TYPE_LABEL).add(size).add(isSigned ? "signed" : "unsigned").toString();
    }
}
