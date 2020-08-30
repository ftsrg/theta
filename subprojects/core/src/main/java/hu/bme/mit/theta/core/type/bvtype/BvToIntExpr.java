package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.CastExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;

public class BvToIntExpr extends CastExpr<BvType, IntType> {

    private static final int HASH_SEED = 6136;
    private static final String OPERATOR_LABEL = "to_int";

    private BvToIntExpr(final Expr<BvType> op) {
        super(op);
    }

    public static BvToIntExpr of(final Expr<BvType> op) {
        return new BvToIntExpr(op);
    }

    public static BvToIntExpr create(final Expr<?> op) {
        final Expr<BvType> newOp = castBv(op);
        return BvToIntExpr.of(newOp);
    }

    @Override
    public IntType getType() {
        return Int();
    }

    @Override
    public IntLitExpr eval(final Valuation val) {
        final BvLitExpr opVal = (BvLitExpr) getOp().eval(val);
        return opVal.toInt();
    }

    @Override
    public BvToIntExpr with(final Expr<BvType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return BvToIntExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof BvToIntExpr) {
            final BvToIntExpr that = (BvToIntExpr) obj;
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
        return OPERATOR_LABEL;
    }
}
