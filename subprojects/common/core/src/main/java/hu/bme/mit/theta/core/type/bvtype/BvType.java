/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.DomainSize;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.*;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;

import java.math.BigInteger;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FromBv;

public class BvType implements Additive<BvType>, Multiplicative<BvType>, Divisible<BvType>,
        Equational<BvType>, Ordered<BvType>,
        Castable<BvType> {

    private final static int HASH_SEED = 5674;
    private final static String TYPE_LABEL = "Bv";

    private final int size;
    private final Boolean signed;

    private volatile int hashCode = 0;

    protected BvType(final int size, Boolean signed) {
        this.signed = signed;
        checkArgument(size > 0);
        this.size = size;
    }

    public static BvType of(final int size) {
        return new BvType(size, null);
    }

    public static BvType of(final int size, final Boolean signed) {
        return new BvType(size, signed);
    }

    public BvType withSize(final int size) {
        return new BvType(size, signed);
    }

    public int getSize() {
        return size;
    }

    public Boolean getSigned() {
        checkState(signed != null);
        return signed;
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
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
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
            return this.getSize() == that.getSize();
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(TYPE_LABEL).add(size).toString();
    }

    @Override
    public AddExpr<BvType> Add(Iterable<? extends Expr<BvType>> ops) {
        return BvExprs.Add(ops);
    }

    @Override
    public SubExpr<BvType> Sub(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvExprs.Sub(leftOp, rightOp);
    }

    @Override
    public PosExpr<BvType> Pos(Expr<BvType> op) {
        return BvExprs.Pos(op);
    }

    @Override
    public NegExpr<BvType> Neg(Expr<BvType> op) {
        return BvExprs.Neg(op);
    }

    @Override
    public <TargetType extends Type> Expr<TargetType> Cast(Expr<BvType> op, TargetType type) {
        if (type instanceof FpType && signed != null) {
            //noinspection unchecked
            return (Expr<TargetType>) FromBv(FpRoundingMode.RTZ, op, (FpType) type, signed);
        }
        throw new ClassCastException("Bv cannot be cast to " + type);
    }

    @Override
    public ModExpr<BvType> Mod(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        checkState(signed != null, "Neutral BvType cannot be used here");
        checkState(signed, "Unsigned BvType cannot be used here");
        return BvExprs.SMod(leftOp, rightOp);
    }

    @Override
    public RemExpr<BvType> Rem(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        checkState(signed != null, "Neutral BvType cannot be used here");
        if (signed) {
            return BvExprs.SRem(leftOp, rightOp);
        } else {
            return BvExprs.URem(leftOp, rightOp);
        }
    }

    @Override
    public MulExpr<BvType> Mul(Iterable<? extends Expr<BvType>> ops) {
        return BvExprs.Mul(ops);
    }

    @Override
    public DivExpr<BvType> Div(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        checkState(signed != null, "Neutral BvType cannot be used here");
        if (signed) {
            return BvExprs.SDiv(leftOp, rightOp);
        } else {
            return BvExprs.UDiv(leftOp, rightOp);
        }
    }

    @Override
    public LtExpr<BvType> Lt(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        checkState(signed != null, "Neutral BvType cannot be used here");
        if (signed) {
            return BvExprs.SLt(leftOp, rightOp);
        } else {
            return BvExprs.ULt(leftOp, rightOp);
        }
    }

    @Override
    public LeqExpr<BvType> Leq(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        checkState(signed != null, "Neutral BvType cannot be used here");
        if (signed) {
            return BvExprs.SLeq(leftOp, rightOp);
        } else {
            return BvExprs.ULeq(leftOp, rightOp);
        }
    }

    @Override
    public GtExpr<BvType> Gt(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        checkState(signed != null, "Neutral BvType cannot be used here");
        if (signed) {
            return BvExprs.SGt(leftOp, rightOp);
        } else {
            return BvExprs.UGt(leftOp, rightOp);
        }
    }

    @Override
    public GeqExpr<BvType> Geq(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        checkState(signed != null, "Neutral BvType cannot be used here");
        if (signed) {
            return BvExprs.SGeq(leftOp, rightOp);
        } else {
            return BvExprs.UGeq(leftOp, rightOp);
        }
    }

    @Override
    public DomainSize getDomainSize() {
        return DomainSize.of(BigInteger.TWO.pow(size));
    }
}
