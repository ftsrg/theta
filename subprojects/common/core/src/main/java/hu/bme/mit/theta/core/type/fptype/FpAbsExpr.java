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
import hu.bme.mit.theta.core.type.UnaryExpr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;

public class FpAbsExpr extends UnaryExpr<FpType, FpType> {

    private static final int HASH_SEED = 6666;
    private static final String OPERATOR_LABEL = "fpabs";

    private FpAbsExpr(final Expr<FpType> op) {
        super(op);
    }

    public static FpAbsExpr of(final Expr<FpType> op) {
        return new FpAbsExpr(castFp(op));
    }

    public static FpAbsExpr create(final Expr<?> op) {
        checkNotNull(op);
        return FpAbsExpr.of(castFp(op));
    }

    @Override
    public FpType getType() {
        return getOp().getType();
    }

    @Override
    public FpLitExpr eval(Valuation val) {
        final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);
        if (opVal.getHidden()) {
            return opVal.neg();
        } else {
            return opVal;
        }
    }

    @Override
    public FpAbsExpr with(final Expr<FpType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return FpAbsExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final FpAbsExpr that = (FpAbsExpr) obj;
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
 
