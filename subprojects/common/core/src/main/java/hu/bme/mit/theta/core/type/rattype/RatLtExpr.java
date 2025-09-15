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
package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.LtExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class RatLtExpr extends LtExpr<RatType> {

    private static final int HASH_SEED = 6311;
    private static final String OPERATOR_LABEL = "<";

    private RatLtExpr(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        super(leftOp, rightOp);
    }

    public static RatLtExpr of(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        return new RatLtExpr(leftOp, rightOp);
    }

    public static RatLtExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
        final Expr<RatType> newLeftOp = cast(leftOp, Rat());
        final Expr<RatType> newRightOp = cast(rightOp, Rat());
        return RatLtExpr.of(newLeftOp, newRightOp);
    }

    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public BoolLitExpr eval(final Valuation val) {
        final RatLitExpr leftOpVal = (RatLitExpr) getLeftOp().eval(val);
        final RatLitExpr rightOpVal = (RatLitExpr) getRightOp().eval(val);
        return leftOpVal.lt(rightOpVal);
    }

    @Override
    public RatLtExpr with(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        if (leftOp == getLeftOp() && rightOp == getRightOp()) {
            return this;
        } else {
            return new RatLtExpr(leftOp, rightOp);
        }
    }

    @Override
    public RatLtExpr withLeftOp(final Expr<RatType> leftOp) {
        return with(leftOp, getRightOp());
    }

    @Override
    public RatLtExpr withRightOp(final Expr<RatType> rightOp) {
        return with(getLeftOp(), rightOp);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final RatLtExpr that = (RatLtExpr) obj;
            return this.getLeftOp().equals(that.getLeftOp())
                    && this.getRightOp().equals(that.getRightOp());
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
