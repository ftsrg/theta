package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.BvUtils;

import java.math.BigInteger;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class BvAddExpr extends AddExpr<BvType> {
    private static final int HASH_SEED = 6586;
    private static final String OPERATOR_LABEL = "+";

    private BvAddExpr(final Iterable<? extends Expr<BvType>> ops) {
        super(ops);
    }

    public static BvAddExpr of(final Iterable<? extends Expr<BvType>> ops) {
        return new BvAddExpr(ops);
    }

    public static BvAddExpr create(final List<? extends Expr<?>> ops) {
        checkArgument(!ops.isEmpty());
        return BvAddExpr.of(ops.stream().map(op -> cast(op, (BvType) ops.get(0).getType())).collect(toImmutableList()));
    }

    @Override
    public BvType getType() {
        return getOps().get(0).getType();
    }

    @Override
    public BvLitExpr eval(final Valuation val) {
        BigInteger sum = BigInteger.ZERO;
        for (final Expr<BvType> op : getOps()) {
            final BvLitExpr opVal = (BvLitExpr) op.eval(val);
            sum = sum.add(BvUtils.bvLitExprToBigInteger(opVal));
        }
        return BvUtils.bigIntegerToBvLitExpr(sum, getType().getSize(), getType().isSigned());
    }

    @Override
    public BvAddExpr with(final Iterable<? extends Expr<BvType>> ops) {
        if (ops == getOps()) {
            return this;
        } else {
            return BvAddExpr.of(ops);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof BvAddExpr) {
            final BvAddExpr that = (BvAddExpr) obj;
            return this.getOps().equals(that.getOps());
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
        return OPERATOR_LABEL;
    }
}
