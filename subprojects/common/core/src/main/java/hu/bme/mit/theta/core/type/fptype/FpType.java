package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.Additive;
import hu.bme.mit.theta.core.type.abstracttype.Castable;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr;
import hu.bme.mit.theta.core.type.abstracttype.GtExpr;
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr;
import hu.bme.mit.theta.core.type.abstracttype.LtExpr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative;
import hu.bme.mit.theta.core.type.abstracttype.NegExpr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.abstracttype.Ordered;
import hu.bme.mit.theta.core.type.abstracttype.PosExpr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;

import static com.google.common.base.Preconditions.checkArgument;

public class FpType implements Additive<FpType>, Multiplicative<FpType>, Equational<FpType>, Ordered<FpType>, Castable<FpType> {
    private final static int HASH_SEED = 5424;
    private final static String TYPE_LABEL = "Fp";

    private final int exponent;
    private final int significand;

    private volatile int hashCode = 0;

    private FpType(final int exponent, final int significand) {
        checkArgument(exponent > 1);
        checkArgument(significand > 1);
        this.exponent = exponent;
        this.significand = significand;
    }

    public static FpType of(final int exponent, final int significand) {
        return new FpType(exponent, significand);
    }

    public int getExponent() {
        return exponent;
    }

    public int getSignificand() {
        return significand;
    }

    @Override
    public AddExpr<FpType> Add(Iterable<? extends Expr<FpType>> ops) {
        return null;
    }

    @Override
    public SubExpr<FpType> Sub(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return null;
    }

    @Override
    public PosExpr<FpType> Pos(Expr<FpType> op) {
        return null;
    }

    @Override
    public NegExpr<FpType> Neg(Expr<FpType> op) {
        return null;
    }

    @Override
    public MulExpr<FpType> Mul(Iterable<? extends Expr<FpType>> ops) {
        return null;
    }

    @Override
    public DivExpr<FpType> Div(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return null;
    }

    @Override
    public EqExpr<FpType> Eq(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return null;
    }

    @Override
    public NeqExpr<FpType> Neq(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return null;
    }

    @Override
    public LtExpr<FpType> Lt(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return null;
    }

    @Override
    public LeqExpr<FpType> Leq(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return null;
    }

    @Override
    public GtExpr<FpType> Gt(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return null;
    }

    @Override
    public GeqExpr<FpType> Geq(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return null;
    }

    @Override
    public <TargetType extends Type> Expr<TargetType> Cast(Expr<FpType> op, TargetType type) {
        return null;
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + exponent;
            result = 31 * result + significand;
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof FpType) {
            final FpType that = (FpType) obj;
            return this.getExponent() == that.getExponent() && this.getSignificand() == that.getSignificand();
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(TYPE_LABEL).add(exponent).add(significand).toString();
    }
}
