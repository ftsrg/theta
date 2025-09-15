/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.NegExpr;

public final class FpNegExpr extends NegExpr<FpType> {

    private static final int HASH_SEED = 4622;
    private static final String OPERATOR_LABEL = "fpneg";

    private FpNegExpr(final Expr<FpType> op) {
        super(op);
    }

    public static FpNegExpr of(final Expr<FpType> op) {
        return new FpNegExpr(op);
    }

    public static FpNegExpr create(final Expr<?> op) {
        final Expr<FpType> newOp = castFp(op);
        return FpNegExpr.of(newOp);
    }

    @Override
    public FpType getType() {
        return getOp().getType();
    }

    @Override
    public FpLitExpr eval(final Valuation val) {
        final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);
        return opVal.neg();
    }

    @Override
    public FpNegExpr with(final Expr<FpType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return FpNegExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final FpNegExpr that = (FpNegExpr) obj;
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
