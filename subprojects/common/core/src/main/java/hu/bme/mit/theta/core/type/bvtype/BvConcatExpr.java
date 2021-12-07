package hu.bme.mit.theta.core.type.bvtype;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;

public final class BvConcatExpr implements Expr<BvType> {
    private static final int HASH_SEED = 8264;
    private static final String OPERATOR_LABEL = "++";

    private final List<Expr<BvType>> ops;

    private volatile int hashCode = 0;

    private BvConcatExpr(final Iterable<? extends Expr<BvType>> ops) {
        checkNotNull(ops);
        checkArgument(ops.iterator().hasNext());
        this.ops = ImmutableList.copyOf(ops);
    }

    public static BvConcatExpr of(final Iterable<? extends Expr<BvType>> ops) {
        return new BvConcatExpr(ops);
    }

    public static BvConcatExpr create(final List<? extends Expr<?>> ops) {
        checkNotNull(ops);
        return BvConcatExpr.of(ops.stream().map(TypeUtils::castBv).collect(toImmutableList()));
    }

    @Override
    public int getArity() {
        return ops.size();
    }

    @Override
    public BvType getType() {
        return BvType.of(ops.stream().map(o -> o.getType().getSize()).reduce(0, Integer::sum));
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
    public List<? extends Expr<BvType>> getOps() {
        return ops;
    }

    @Override
    public Expr<BvType> withOps(List<? extends Expr<?>> ops) {
        checkNotNull(ops);
        checkArgument(ops.size() >= 1);

        return of(ops.stream().map(TypeUtils::castBv).collect(toImmutableList()));
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + getOps().hashCode();
            hashCode = result;
        }
        return result;
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
    public String toString() {
        return Utils.lispStringBuilder(OPERATOR_LABEL).addAll(getOps()).toString();
    }
}
