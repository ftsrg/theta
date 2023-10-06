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
package hu.bme.mit.theta.core.type.anytype;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.*;

import static com.google.common.base.Preconditions.checkNotNull;

public final class DeRefExpr<ExprType extends Type> extends UnaryExpr<ExprType, ExprType> {

    private static final String OPERATOR_LABEL = "*";
    private static final int HASH_SEED = 45611;

    private DeRefExpr(final Expr<ExprType> op) {
        super(op);
    }

    public static <ExprType extends Type> DeRefExpr<ExprType> of(final Expr<ExprType> op) {
        return new DeRefExpr<>(op);
    }

    @Override
    public final ExprType getType() {
        return getOp().getType();
    }

    @Override
    public LitExpr<ExprType> eval(final Valuation val) {
        throw new UnsupportedOperationException();
    }

    @Override
    public final UnaryExpr<ExprType, ExprType> with(final Expr<ExprType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return DeRefExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final DeRefExpr<?> that = (DeRefExpr<?>) obj;
            return this.getOp().equals(that.getOp());
        } else {
            return false;
        }
    }

    @Override
    protected final int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public final String getOperatorLabel() {
        return OPERATOR_LABEL;
    }
}