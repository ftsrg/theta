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
package hu.bme.mit.theta.common;

import com.google.common.collect.ImmutableList;

import java.util.function.Function;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Tuple1<T1> extends Tuple {

    private Tuple1(final T1 e1) {
        super(ImmutableList.of(e1));
    }

    public static <T1> Tuple1<T1> of(final T1 e1) {
        return new Tuple1<>(e1);
    }

    public T1 get1() {
        @SuppressWarnings("unchecked") final T1 result = (T1) elem(0);
        return result;
    }

    public <R> R unpackTo(final Function<? super T1, R> function) {
        checkNotNull(function);
        return function.apply(get1());
    }

}
