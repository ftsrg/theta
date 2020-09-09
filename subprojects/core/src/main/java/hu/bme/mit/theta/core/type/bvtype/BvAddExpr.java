package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.MultiaryExpr;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public final class BvAddExpr extends MultiaryExpr<BvType, BvType> {
    private static final int HASH_SEED = 6586;
    private static final String OPERATOR_LABEL = "bvadd";

    private BvAddExpr(final Iterable<? extends Expr<BvType>> ops) {
        super(ops);
        checkAllTypesEqual(ops);
    }

    public static BvAddExpr of(final Iterable<? extends Expr<BvType>> ops) {
        return new BvAddExpr(ops);
    }

    public static BvAddExpr create(final List<? extends Expr<?>> ops) {
        checkNotNull(ops);
        return BvAddExpr.of(ops.stream().map(TypeUtils::castBv).collect(toImmutableList()));
    }

    @Override
    public BvType getType() {
        return getOps().get(0).getType();
    }

    @Override
    public BvLitExpr eval(final Valuation val) {
        return getOps().stream().skip(1).reduce(
            (BvLitExpr) getOps().get(0).eval(val),
            (op1, op2) -> (op1.add((BvLitExpr) op2.eval(val))),
            BvLitExpr::add
        );
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
