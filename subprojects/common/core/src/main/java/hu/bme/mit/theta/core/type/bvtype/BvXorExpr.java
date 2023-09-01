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

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.MultiaryExpr;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public final class BvXorExpr extends MultiaryExpr<BvType, BvType> {

    private static final int HASH_SEED = 9457;
    private static final String OPERATOR_LABEL = "bvxor";

    private BvXorExpr(final Iterable<? extends Expr<BvType>> ops) {
        super(ops);
        checkAllTypesEqual(ops);
    }

    public static BvXorExpr of(final Iterable<? extends Expr<BvType>> ops) {
        return new BvXorExpr(ops);
    }

    public static BvXorExpr create(final List<? extends Expr<?>> ops) {
        checkNotNull(ops);
        return BvXorExpr.of(ops.stream().map(TypeUtils::castBv).collect(toImmutableList()));
    }

    @Override
    public BvType getType() {
        return getOps().get(0).getType();
    }

    @Override
    public BvLitExpr eval(final Valuation val) {
        return getOps().stream().skip(1).reduce(
                (BvLitExpr) getOps().get(0).eval(val),
                (op1, op2) -> (op1.xor((BvLitExpr) op2.eval(val))),
                BvLitExpr::xor
        );
    }

    @Override
    public BvXorExpr with(final Iterable<? extends Expr<BvType>> ops) {
        if (ops == getOps()) {
            return this;
        } else {
            return BvXorExpr.of(ops);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final BvXorExpr that = (BvXorExpr) obj;
            return this.getOps().equals(that.getOps());
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
