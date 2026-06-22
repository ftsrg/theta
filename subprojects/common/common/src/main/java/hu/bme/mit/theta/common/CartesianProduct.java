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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class CartesianProduct {

    public static <T> List<List<T>> of(final List<? extends Collection<? extends T>> collections) {
        List<List<T>> accum = List.of(List.of());
        for (final Collection<? extends T> next : collections) {
            accum = append(accum, next);
        }
        return accum;
    }

    private static <T> List<List<T>> append(List<List<T>> current, Collection<? extends T> next) {
        final ArrayList<List<T>> result = new ArrayList<>(current.size() * next.size());
        for (final List<T> toGrow : current) {
            int newSize = toGrow.size() + 1;
            for (final T element : next) {
                final List<T> newList = new ArrayList<>(newSize);
                newList.addAll(toGrow);
                newList.add(element);
                result.add(newList);
            }
        }
        return result;
    }
}
