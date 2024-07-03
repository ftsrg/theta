/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;

public final class BvSExtExpr implements Expr<BvType> {

    private static final int HASH_SEED = 6126;
    private static final String OPERATOR_LABEL = "bv_sign_extend";

    private final Expr<BvType> op;
    private final BvType extendType;

    private volatile int hashCode = 0;

    private BvSExtExpr(final Expr<BvType> op, final BvType extendType) {
        checkNotNull(op);
        checkNotNull(extendType);
        checkArgument(extendType.getSize() >= op.getType().getSize());

        this.op = op;
        this.extendType = extendType;
    }

    public static BvSExtExpr of(final Expr<BvType> op, final BvType extendType) {
        return new BvSExtExpr(op, extendType);
    }

    public static BvSExtExpr create(final Expr<?> op, final BvType extendType) {
        return new BvSExtExpr(castBv(op), extendType);
    }

    public Expr<BvType> getOp() {
        return op;
    }

    public BvType getExtendType() {
        return extendType;
    }

    @Override
    public int getArity() {
        return 1;
    }

    @Override
    public BvType getType() {
        return extendType;
    }

    @Override
    public LitExpr<BvType> eval(Valuation val) {
        final BvLitExpr bvLitExpr = (BvLitExpr) op.eval(val);
        return bvLitExpr.sext(extendType);
    }

    @Override
    public List<? extends Expr<?>> getOps() {
        return ImmutableList.of(op);
    }

    @Override
    public Expr<BvType> withOps(List<? extends Expr<?>> ops) {
        checkNotNull(ops);
        checkArgument(ops.size() == 1);
        final Expr<BvType> newBitvec = castBv(ops.get(0));
        return of(newBitvec, extendType);
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + op.hashCode();
            result = 31 * result + extendType.hashCode();
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final BvSExtExpr that = (BvSExtExpr) obj;
            return this.getOps().equals(that.getOps()) && this.getType().equals(that.getType());
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(OPERATOR_LABEL).body().add(getOp()).add(getType()).toString();
    }
}
