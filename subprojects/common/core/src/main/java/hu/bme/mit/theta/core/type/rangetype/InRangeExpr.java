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

package hu.bme.mit.theta.core.type.rangetype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class InRangeExpr extends UnaryExpr<IntType, BoolType> {

    private static final int HASH_SEED = 4538;

    private final RangeType range;

    private InRangeExpr(final Expr<IntType> op, final RangeType range) {
        super(op);
        this.range = range;
    }

    public static InRangeExpr of(final Expr<IntType> op, final RangeType range) {
        return new InRangeExpr(op, range);
    }

    @Override
    public UnaryExpr<IntType, BoolType> with(final Expr<IntType> op) {
        return InRangeExpr.of(op, range);
    }

    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public LitExpr<BoolType> eval(final Valuation val) {
        final IntLitExpr litExpr = (IntLitExpr) getOp().eval(val);
        final int value = litExpr.getValue().intValue();
        return Bool(range.getLower() <= value && value <= range.getUpper());
    }

    public RangeType getRange() {
        return range;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof InRangeExpr) {
            final InRangeExpr that = (InRangeExpr) obj;
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
        return "in " + range;
    }
}
