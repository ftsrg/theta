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
package hu.bme.mit.theta.core.type.arraytype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class ArrayNeqExpr<IndexType extends Type, ElemType extends Type>
        extends NeqExpr<ArrayType<IndexType, ElemType>> {

    private static final int HASH_SEED = 5233;
    private static final String OPERATOR_LABEL = "/=";

    private ArrayNeqExpr(final Expr<ArrayType<IndexType, ElemType>> leftOp,
                         final Expr<ArrayType<IndexType, ElemType>> rightOp) {
        super(leftOp, rightOp);
    }

    public static <IndexType extends Type, ElemType extends Type> ArrayNeqExpr<IndexType, ElemType> of(
            final Expr<ArrayType<IndexType, ElemType>> leftOp,
            final Expr<ArrayType<IndexType, ElemType>> rightOp) {
        return new ArrayNeqExpr<>(leftOp, rightOp);
    }

    public static <IndexType extends Type, ElemType extends Type> ArrayNeqExpr<?, ?> create(
            final Expr<?> leftOp,
            final Expr<?> rightOp) {
        @SuppressWarnings("unchecked") final ArrayType<IndexType, ElemType> arrayType = (ArrayType<IndexType, ElemType>) leftOp.getType();
        final Expr<ArrayType<IndexType, ElemType>> newLeftOp = cast(leftOp, arrayType);
        final Expr<ArrayType<IndexType, ElemType>> newRightOp = cast(rightOp, arrayType);
        return ArrayNeqExpr.of(newLeftOp, newRightOp);
    }

    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public LitExpr<BoolType> eval(final Valuation val) {
        throw new UnsupportedOperationException();
    }

    @Override
    public BinaryExpr<ArrayType<IndexType, ElemType>, BoolType> with(
            final Expr<ArrayType<IndexType, ElemType>> leftOp,
            final Expr<ArrayType<IndexType, ElemType>> rightOp) {
        if (leftOp == getLeftOp() && rightOp == getRightOp()) {
            return this;
        } else {
            return new ArrayNeqExpr<>(leftOp, rightOp);
        }
    }

    @Override
    public BinaryExpr<ArrayType<IndexType, ElemType>, BoolType> withLeftOp(
            final Expr<ArrayType<IndexType, ElemType>> leftOp) {
        return with(leftOp, getRightOp());
    }

    @Override
    public BinaryExpr<ArrayType<IndexType, ElemType>, BoolType> withRightOp(
            final Expr<ArrayType<IndexType, ElemType>> rightOp) {
        return with(getLeftOp(), rightOp);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final ArrayNeqExpr<?, ?> that = (ArrayNeqExpr<?, ?>) obj;
            return this.getLeftOp().equals(that.getLeftOp()) && this.getRightOp()
                    .equals(that.getRightOp());
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
