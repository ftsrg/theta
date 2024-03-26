/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;

import java.util.List;
import java.util.Objects;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class Dereference<A extends Type, T extends Type> implements Expr<T> {

    private static final String OPERATOR_LABEL = "deref";
    private final Expr<A> array;
    private final Expr<A> offset;
    private final T type;

    private Dereference(Expr<A> array, Expr<A> offset, T type) {
        this.array = array;
        this.offset = offset;
        this.type = type;
    }

    public Expr<A> getArray() {
        return array;
    }

    public Expr<A> getOffset() {
        return offset;
    }


    public static <A extends Type, T extends Type> Dereference<A, T> of(Expr<A> array, Expr<A> offset, T type) {
        return new Dereference<>(array, offset, type);
    }

    @Override
    public int getArity() {
        return 2;
    }

    @Override
    public T getType() {
        return type;
    }

    @Override
    public LitExpr<T> eval(Valuation val) {
        throw new IllegalStateException(
                "Reference/Dereference expressions are not meant to be evaluated!");
    }

    @Override
    public List<? extends Expr<?>> getOps() {
        return List.of(array, offset);
    }

    @Override
    public Expr<T> withOps(List<? extends Expr<?>> ops) {
        checkState(ops.size() == 2);
        @SuppressWarnings("unchecked") final T ptrType = (T) ops.get(0).getType();
        return Dereference.of(cast(ops.get(0), ptrType), cast(ops.get(1), ptrType), type);
    }

    @Override
    public int hashCode() {
        return Objects.hash(array, offset, type);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Dereference<?, ?> that) {
            return Objects.equals(this.array, that.array) &&
                    Objects.equals(this.offset, that.offset) &&
                    Objects.equals(this.type, that.type);
        }
        return false;
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(OPERATOR_LABEL).add(getArray()).add(getOffset()).add(type)
                .toString();
    }
}
