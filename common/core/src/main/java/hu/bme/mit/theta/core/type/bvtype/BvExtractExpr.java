package hu.bme.mit.theta.core.type.bvtype;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;

import java.math.BigInteger;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;

public final class BvExtractExpr implements Expr<BvType> {
    private static final int HASH_SEED = 6586;
    private static final String OPERATOR_LABEL = "extract";

    private final Expr<BvType> bitvec;
    private final IntLitExpr from;
    private final IntLitExpr until;

    private volatile int hashCode = 0;

    private BvExtractExpr(final Expr<BvType> bitvec, final IntLitExpr from, final IntLitExpr until) {
        checkNotNull(bitvec);
        checkNotNull(from);
        checkNotNull(until);
        checkArgument(from.getValue().compareTo(BigInteger.ZERO) >= 0);
        checkArgument(until.getValue().compareTo(BigInteger.ZERO) >= 0);
        checkArgument(until.getValue().compareTo(from.getValue()) > 0);

        this.bitvec = bitvec;
        this.from = from;
        this.until = until;
    }

    public static BvExtractExpr of(final Expr<BvType> bitvec, final IntLitExpr from, final IntLitExpr until) {
        return new BvExtractExpr(bitvec, from, until);
    }

    public static BvExtractExpr create(final Expr<?> bitvec, final Expr<?> from, final Expr<?> until) {
        final Expr<BvType> newBitvec = castBv(bitvec);
        final IntLitExpr newFrom = (IntLitExpr) cast(from, Int());
        final IntLitExpr newUntil = (IntLitExpr) cast(until, Int());
        return BvExtractExpr.of(newBitvec, newFrom, newUntil);
    }

    public Expr<BvType> getBitvec() {
        return bitvec;
    }

    public IntLitExpr getFrom() {
        return from;
    }

    public IntLitExpr getUntil() {
        return until;
    }

    @Override
    public List<? extends Expr<?>> getOps() {
        return ImmutableList.of(bitvec, from, until);
    }

    @Override
    public int getArity() {
        return 3;
    }

    @Override
    public BvType getType() {
        return BvType.of(until.getValue().subtract(from.getValue()).intValue());
    }

    @Override
    public LitExpr<BvType> eval(Valuation val) {
        final BvLitExpr bvLitExpr = (BvLitExpr) bitvec.eval(val);
        return bvLitExpr.extract(from, until);
    }

    @Override
    public Expr<BvType> withOps(List<? extends Expr<?>> ops) {
        checkNotNull(ops);
        checkArgument(ops.size() == 3);
        final Expr<BvType> newBitvec = castBv(ops.get(0));
        final IntLitExpr newFrom = (IntLitExpr) cast(ops.get(1), Int());
        final IntLitExpr newUntil = (IntLitExpr) cast(ops.get(2), Int());

        if(bitvec.equals(newBitvec) && from.equals(newFrom) && until.equals(newUntil)) {
            return this;
        }
        else {
            return of(newBitvec, newFrom, newUntil);
        }
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + bitvec.hashCode();
            result = 31 * result + from.hashCode();
            result = 31 * result + until.hashCode();
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof BvExtractExpr) {
            final BvExtractExpr that = (BvExtractExpr) obj;
            return this.getBitvec().equals(that.getBitvec()) && this.getFrom().equals(that.getFrom())
                && this.getUntil().equals(that.getUntil());
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(OPERATOR_LABEL).add(getBitvec()).add(getFrom()).add(getUntil()).toString();
    }
}
