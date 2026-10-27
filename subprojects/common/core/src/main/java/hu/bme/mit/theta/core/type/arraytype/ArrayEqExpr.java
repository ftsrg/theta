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
package hu.bme.mit.theta.core.type.arraytype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class ArrayEqExpr<IndexType extends Type, ElemType extends Type>
        extends EqExpr<ArrayType<IndexType, ElemType>> {

    private static final int HASH_SEED = 4261;
    private static final String OPERATOR_LABEL = "=";

    private ArrayEqExpr(
            final Expr<ArrayType<IndexType, ElemType>> leftOp,
            final Expr<ArrayType<IndexType, ElemType>> rightOp) {
        super(leftOp, rightOp);
    }

    public static <IndexType extends Type, ElemType extends Type>
            ArrayEqExpr<IndexType, ElemType> of(
                    final Expr<ArrayType<IndexType, ElemType>> leftOp,
                    final Expr<ArrayType<IndexType, ElemType>> rightOp) {
        return new ArrayEqExpr<>(leftOp, rightOp);
    }

    public static <IndexType extends Type, ElemType extends Type> ArrayEqExpr<?, ?> create(
            final Expr<?> leftOp, final Expr<?> rightOp) {
        @SuppressWarnings("unchecked")
        final ArrayType<IndexType, ElemType> arrayType =
                (ArrayType<IndexType, ElemType>) leftOp.getType();
        final Expr<ArrayType<IndexType, ElemType>> newLeftOp = cast(leftOp, arrayType);
        final Expr<ArrayType<IndexType, ElemType>> newRightOp = cast(rightOp, arrayType);
        return ArrayEqExpr.of(newLeftOp, newRightOp);
    }

    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public LitExpr<BoolType> eval(final Valuation val) {
        return Bool(evalEquals(getLeftOp(), getRightOp(), val));
    }

    static boolean evalEquals(
            final Expr<? extends ArrayType<?, ?>> leftOp,
            final Expr<? extends ArrayType<?, ?>> rightOp,
            final Valuation val) {
        final LitExpr<?> left = leftOp.eval(val);
        final LitExpr<?> right = rightOp.eval(val);
        if (!(left instanceof ArrayLitExpr<?, ?> leftArray)
                || !(right instanceof ArrayLitExpr<?, ?> rightArray)) {
            throw new UnsupportedOperationException(
                    "Cannot evaluate equality of non-literal array values: " + left + ", " + right);
        }
        return literalsEqual(leftArray, rightArray);
    }

    /**
     * Extensional equality of two array literals: the default elements agree and the elements agree
     * at every index mentioned in either literal (a missing index reads as the default element; for
     * a repeated index the first occurrence counts, as in {@link ArrayReadExpr#eval}).
     */
    private static boolean literalsEqual(
            final ArrayLitExpr<?, ?> left, final ArrayLitExpr<?, ?> right) {
        if (!valuesEqual(left.getElseElem(), right.getElseElem())) {
            return false;
        }
        for (final var elem : left.getElements()) {
            if (!valuesEqual(elem.get2(), readLit(right, elem.get1()))) {
                return false;
            }
        }
        for (final var elem : right.getElements()) {
            if (!valuesEqual(readLit(left, elem.get1()), elem.get2())) {
                return false;
            }
        }
        return true;
    }

    private static LitExpr<?> readLit(final ArrayLitExpr<?, ?> array, final LitExpr<?> index) {
        for (final var elem : array.getElements()) {
            if (elem.get1().equals(index)) {
                return elem.get2();
            }
        }
        return array.getElseElem();
    }

    private static boolean valuesEqual(final LitExpr<?> a, final LitExpr<?> b) {
        if (a instanceof ArrayLitExpr<?, ?> aa && b instanceof ArrayLitExpr<?, ?> bb) {
            return literalsEqual(aa, bb);
        }
        return a.equals(b);
    }

    @Override
    public BinaryExpr<ArrayType<IndexType, ElemType>, BoolType> with(
            final Expr<ArrayType<IndexType, ElemType>> leftOp,
            final Expr<ArrayType<IndexType, ElemType>> rightOp) {
        if (leftOp == getLeftOp() && rightOp == getRightOp()) {
            return this;
        } else {
            return ArrayEqExpr.of(leftOp, rightOp);
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
            final ArrayEqExpr<?, ?> that = (ArrayEqExpr<?, ?>) obj;
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
