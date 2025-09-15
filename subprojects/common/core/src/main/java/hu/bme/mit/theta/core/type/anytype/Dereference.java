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
package hu.bme.mit.theta.core.type.anytype;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

public final class Dereference<A extends Type, O extends Type, T extends Type> implements Expr<T> {

    private static final String OPERATOR_LABEL = "deref";
    private final Expr<A> array;
    private final Expr<O> offset;
    private final T type;

    private final Optional<Expr<IntType>> uniquenessIdx;

    private Dereference(Expr<A> array, Expr<O> offset, T type) {
        this.array = array;
        this.offset = offset;
        this.type = type;
        uniquenessIdx = Optional.empty();
    }

    private Dereference(Expr<A> array, Expr<O> offset, Expr<IntType> uniqueness, T type) {
        this.array = array;
        this.offset = offset;
        this.type = type;
        this.uniquenessIdx = Optional.ofNullable(uniqueness);
    }

    public Expr<A> getArray() {
        return array;
    }

    public Expr<O> getOffset() {
        return offset;
    }

    public static <A extends Type, O extends Type, T extends Type> Dereference<A, O, T> of(
            Expr<A> array, Expr<O> offset, T type) {
        return new Dereference<>(array, offset, type);
    }

    private static <A extends Type, O extends Type, T extends Type> Dereference<A, O, T> of(
            Expr<A> array, Expr<O> offset, Expr<IntType> uniqueness, T type) {
        return new Dereference<>(array, offset, uniqueness, type);
    }

    public Dereference<A, O, T> withUniquenessExpr(Expr<IntType> expr) {
        return Dereference.of(array, offset, expr, type); // TODO: this kills the stuck check
    }

    @Override
    public int getArity() {
        return 3;
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
        return uniquenessIdx.isPresent()
                ? List.of(array, offset, uniquenessIdx.get())
                : List.of(array, offset);
    }

    @Override
    public Expr<T> withOps(List<? extends Expr<?>> ops) {
        checkState(ops.size() == 3 || ops.size() == 2);
        if (ops.size() == 3) {
            return Dereference.of(ops.get(0), ops.get(1), (Expr<IntType>) ops.get(2), type);
        } else {
            return Dereference.of(ops.get(0), ops.get(1), type);
        }
    }

    @Override
    public int hashCode() {
        return Objects.hash(array, offset, uniquenessIdx, type);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Dereference<?, ?, ?> that) {
            return Objects.equals(this.array, that.array)
                    && Objects.equals(this.offset, that.offset)
                    && Objects.equals(this.uniquenessIdx, that.uniquenessIdx)
                    && Objects.equals(this.type, that.type);
        }
        return false;
    }

    @Override
    public String toString() {
        var base = Utils.lispStringBuilder(OPERATOR_LABEL).body().add(getArray()).add(getOffset());
        uniquenessIdx.ifPresent(base::add);
        return base.add(type).toString();
    }

    public Optional<Expr<IntType>> getUniquenessIdx() {
        return uniquenessIdx;
    }
}
