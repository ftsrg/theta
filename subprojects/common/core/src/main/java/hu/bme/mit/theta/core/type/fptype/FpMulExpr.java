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
package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public class FpMulExpr extends MulExpr<FpType> {

    private static final int HASH_SEED = 4276;
    private static final String OPERATOR_LABEL = "fpmul";

    private final FpRoundingMode roundingMode;

    private FpMulExpr(final FpRoundingMode roundingMode,
                      final Iterable<? extends Expr<FpType>> ops) {
        super(ops);
        checkAllTypesEqual(ops);
        checkNotNull(roundingMode);
        this.roundingMode = roundingMode;
    }

    public static FpMulExpr of(final FpRoundingMode roundingMode,
                               final Iterable<? extends Expr<FpType>> ops) {
        return new FpMulExpr(roundingMode, ops);
    }

    public static FpMulExpr create(final FpRoundingMode roundingMode,
                                   final List<? extends Expr<?>> ops) {
        checkNotNull(ops);
        return FpMulExpr.of(roundingMode,
                ops.stream().map(TypeUtils::castFp).collect(toImmutableList()));
    }

    public FpRoundingMode getRoundingMode() {
        return roundingMode;
    }

    @Override
    public FpType getType() {
        return getOps().get(0).getType();
    }

    @Override
    public FpLitExpr eval(final Valuation val) {
        return getOps().stream().skip(1).reduce(
                (FpLitExpr) getOps().get(0).eval(val),
                (op1, op2) -> (op1.mul(roundingMode, (FpLitExpr) op2.eval(val))),
                (op1, op2) -> (op1.mul(roundingMode, op2))
        );
    }

    @Override
    public FpMulExpr with(final Iterable<? extends Expr<FpType>> ops) {
        if (ops == getOps()) {
            return this;
        } else {
            return FpMulExpr.of(roundingMode, ops);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final FpMulExpr that = (FpMulExpr) obj;
            return this.getOps().equals(that.getOps()) && roundingMode == that.roundingMode;
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
 
