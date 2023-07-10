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

import java.util.function.Function;

import static com.google.common.base.Preconditions.checkNotNull;

@FunctionalInterface
public interface QuintFunction<T, U, V, W, X, R> {

    R apply(T t, U u, V v, W w, X x);

    default <RR> QuintFunction<T, U, V, W, X, RR> andThen(
            final Function<? super R, ? extends RR> after) {
        checkNotNull(after);
        return (final T t, final U u, final V v, final W w, final X x) -> after.apply(
                apply(t, u, v, w, x));
    }
}
