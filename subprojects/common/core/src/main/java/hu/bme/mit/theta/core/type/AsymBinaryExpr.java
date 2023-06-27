package hu.bme.mit.theta.core.type;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.abstracttype.LtExpr;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public abstract class AsymBinaryExpr<LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> implements Expr<ExprType> {

    private final Expr<LeftOpType> leftOp;
    private final Expr<RightOpType> rightOp;

    private volatile int hashCode = 0;

    protected AsymBinaryExpr(final Expr<LeftOpType> leftOp, final Expr<RightOpType> rightOp) {
        this.leftOp = checkNotNull(leftOp);
        this.rightOp = checkNotNull(rightOp);
    }

    public final Expr<LeftOpType> getLeftOp() {
        return leftOp;
    }

    public final Expr<RightOpType> getRightOp() {
        return rightOp;
    }

    @Override
    public int getArity() {
        return 2;
    }

    @Override
    public List<Expr<? extends Type>> getOps() {
        return ImmutableList.of(leftOp, rightOp);
    }

    @Override
    public Expr<ExprType> withOps(List<? extends Expr<?>> ops) {
        checkNotNull(ops);
        checkArgument(ops.size() == 2);
        final LeftOpType leftOpType = getLeftOp().getType();
        final Expr<LeftOpType> newLeftOp = TypeUtils.cast(ops.get(0), leftOpType);
        final RightOpType rightOpType = getRightOp().getType();
        final Expr<RightOpType> newRightOp = TypeUtils.cast(ops.get(1), rightOpType);
        return with(newLeftOp, newRightOp);
    }

    @Override
    public final int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = getHashSeed();
            result = 31 * result + getLeftOp().hashCode();
            result = 31 * result + getRightOp().hashCode();
            hashCode = result;
        }
        return result;
    }

    @Override
    public final String toString() {
        return Utils.lispStringBuilder(getOperatorLabel()).add(leftOp).add(rightOp).toString();
    }

    public abstract AsymBinaryExpr<LeftOpType, RightOpType, ExprType> with(final Expr<LeftOpType> leftOp, final Expr<RightOpType> rightOp);

    public abstract AsymBinaryExpr<LeftOpType, RightOpType, ExprType> withLeftOp(final Expr<LeftOpType> leftOp);

    public abstract AsymBinaryExpr<LeftOpType, RightOpType, ExprType> withRightOp(final Expr<RightOpType> rightOp);

    protected abstract int getHashSeed();

    public abstract String getOperatorLabel();
}
