package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.MultiaryExpr;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;

public final class BvConcatExpr extends MultiaryExpr<BvType, BvType> {
    private static final int HASH_SEED = 8264;
    private static final String OPERATOR_LABEL = "++";

    private BvConcatExpr(final Iterable<? extends Expr<BvType>> ops) {
        super(ops);
        checkArgument(ops.iterator().hasNext(), "It needs to have at least one operand");
    }

    public static BvConcatExpr of(final Iterable<? extends Expr<BvType>> ops) {
        return new BvConcatExpr(ops);
    }

    public static BvConcatExpr create(final List<? extends Expr<?>> ops) {
        checkNotNull(ops);
        return BvConcatExpr.of(ops.stream().map(TypeUtils::castBv).collect(toImmutableList()));
    }

    @Override
    public BvType getType() {
        return BvType.of(getOps().stream().map(e -> e.getType().getSize()).reduce(0, Integer::sum));
    }

    @Override
    public BvLitExpr eval(final Valuation val) {
        return getOps().stream().skip(1).reduce(
            (BvLitExpr) getOps().get(0).eval(val),
            (op1, op2) -> (op1.concat((BvLitExpr) op2.eval(val))),
            BvLitExpr::concat
        );
    }

    @Override
    public BvConcatExpr with(final Iterable<? extends Expr<BvType>> ops) {
        if (ops == getOps()) {
            return this;
        } else {
            return BvConcatExpr.of(ops);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof BvConcatExpr) {
            final BvConcatExpr that = (BvConcatExpr) obj;
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
