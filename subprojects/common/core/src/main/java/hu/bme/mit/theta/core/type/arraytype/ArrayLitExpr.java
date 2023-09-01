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

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprSimplifier;

import java.util.List;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public final class ArrayLitExpr<IndexType extends Type, ElemType extends Type> extends NullaryExpr<ArrayType<IndexType, ElemType>>
        implements LitExpr<ArrayType<IndexType, ElemType>> {

    private static final int HASH_SEED = 229;
    private static final String OPERATOR_LABEL = "array";

    private final ArrayType<IndexType, ElemType> type;

    private final List<Tuple2<LitExpr<IndexType>, LitExpr<ElemType>>> elems;

    private final LitExpr<ElemType> elseElem;

    private volatile int hashCode;

    private ArrayLitExpr(final List<Tuple2<? extends Expr<IndexType>, ? extends Expr<ElemType>>> elems,
                         final Expr<ElemType> elseElem, final ArrayType<IndexType, ElemType> type) {
        this.type = checkNotNull(type);
        final ExprSimplifier exprSimplifier = ExprSimplifier.create();
        Expr<ElemType> simplifiedElem = exprSimplifier.simplify(checkNotNull(elseElem), ImmutableValuation.empty());
        checkState(simplifiedElem instanceof LitExpr, "ArrayLitExprs shall only contain literal values!");
        this.elseElem = (LitExpr<ElemType>) simplifiedElem;
        this.elems = checkNotNull(elems).stream().map(elem -> {
            Expr<IndexType> index = exprSimplifier.simplify(elem.get1(), ImmutableValuation.empty());
            Expr<ElemType> element = exprSimplifier.simplify(elem.get2(), ImmutableValuation.empty());
            checkState(index instanceof LitExpr && element instanceof LitExpr, "ArrayLitExprs shall only contain literal values");
            return Tuple2.of((LitExpr<IndexType>) index, (LitExpr<ElemType>) element);
        }).collect(Collectors.toList());
    }

    public static <IndexType extends Type, ElemType extends Type> ArrayLitExpr<IndexType, ElemType> of(
            final List<Tuple2<? extends Expr<IndexType>, ? extends Expr<ElemType>>> elems,
            final Expr<ElemType> elseElem,
            final ArrayType<IndexType, ElemType> type) {
        return new ArrayLitExpr<>(elems, elseElem, type);
    }

    public List<Tuple2<LitExpr<IndexType>, LitExpr<ElemType>>> getElements() {
        return ImmutableList.copyOf(elems);
    }

    public LitExpr<ElemType> getElseElem() {
        return elseElem;
    }

    @Override
    public ArrayType<IndexType, ElemType> getType() {
        return type;
    }

    @Override
    public LitExpr<ArrayType<IndexType, ElemType>> eval(final Valuation val) {
        return this;
    }

    @Override
    public int hashCode() {
        int tmp = hashCode;
        if (tmp == 0) {
            tmp = HASH_SEED;
            tmp = 31 * tmp + type.hashCode();
            for (Tuple2<LitExpr<IndexType>, LitExpr<ElemType>> elem : elems) {
                tmp = 31 * tmp + elem.hashCode();
            }
            hashCode = tmp;
        }
        return tmp;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final ArrayLitExpr<?, ?> that = (ArrayLitExpr<?, ?>) obj;
            return this.type.equals(that.type) && this.elems.equals(that.elems) && elseElem.equals(that.elseElem);
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(OPERATOR_LABEL)
                .addAll(elems.stream().map(elem -> String.format("(%s %s)", elem.get1(), elem.get2())))
                .add((String.format("(default %s)", elseElem)))
                .toString();
    }

}
