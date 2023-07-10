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

import java.util.Comparator;
import java.util.Objects;

@FunctionalInterface
public interface TernaryOperator<T> extends TriFunction<T, T, T, T> {

    public static <T> TernaryOperator<T> minBy(final Comparator<? super T> comparator) {
        Objects.requireNonNull(comparator);
        return (a, b, c) -> comparator.compare(a, b) <= 0 ? (comparator.compare(a, c) <= 0 ? a : c)
                : (comparator.compare(b, c) <= 0 ? b : c);
    }

    public static <T> TernaryOperator<T> maxBy(final Comparator<? super T> comparator) {
        Objects.requireNonNull(comparator);
        return (a, b, c) -> comparator.compare(a, b) >= 0 ? (comparator.compare(a, c) >= 0 ? a : c)
                : (comparator.compare(b, c) >= 0 ? b : c);
    }

}
