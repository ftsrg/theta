/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.core.type.inttype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.utils.BvUtils;

public class IntToBvExpr extends UnaryExpr<IntType, BvType> {
    private static final int HASH_SEED = 6384;
    private static final String OPERATOR_LABEL = "int_to_bv";

    private final Expr<IntType> op;
    private final int size;

    private IntToBvExpr(final Expr<IntType> op, final int size) {
        super(op);
        this.op = op;
        this.size = size;
    }

    public static IntToBvExpr of(final Expr<IntType> op, final int size) {
       return new IntToBvExpr(op, size);
    }

    public static IntToBvExpr create(final Expr<IntType> op, final int size) {
        return IntToBvExpr.of(op, size);
    }

    public int getSize() {
        return size;
    }

    @Override
    public BvType getType() {
        return BvType.of(size);
    }

    @Override
    public BvLitExpr eval(Valuation val) {
        final IntLitExpr op = (IntLitExpr) this.op.eval(val);
        return BvUtils.bigIntegerToNeutralBvLitExpr(op.getValue(), size);
    }

    @Override
    public IntToBvExpr with(Expr<IntType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return IntToBvExpr.of(op, size);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final IntToBvExpr that = (IntToBvExpr) obj;
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
