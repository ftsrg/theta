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
package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import java.util.function.BiFunction;

public final class Tuple2<T1, T2> extends Tuple {

    private Tuple2(final T1 e1, final T2 e2) {
        super(ImmutableList.of(e1, e2));
    }

    public static <T1, T2> Tuple2<T1, T2> of(final T1 e1, final T2 e2) {
        return new Tuple2<>(e1, e2);
    }

    public T1 get1() {
        @SuppressWarnings("unchecked")
        final T1 result = (T1) elem(0);
        return result;
    }

    public T2 get2() {
        @SuppressWarnings("unchecked")
        final T2 result = (T2) elem(1);
        return result;
    }

    public <R> R unpackTo(final BiFunction<? super T1, ? super T2, R> function) {
        checkNotNull(function);
        return function.apply(get1(), get2());
    }
}
