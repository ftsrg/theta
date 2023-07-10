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
package hu.bme.mit.theta.solver;

import java.util.Arrays;
import java.util.List;

public final class ItpMarkerTree<T extends ItpMarker> {

    private final T marker;
    private final List<ItpMarkerTree<T>> children;

    private ItpMarkerTree(final T marker, final List<ItpMarkerTree<T>> children) {
        this.marker = marker;
        this.children = children;
    }

    public T getMarker() {
        return marker;
    }

    public List<ItpMarkerTree<T>> getChildren() {
        return children;
    }

    public ItpMarkerTree<T> getChild(int i) {
        return children.get(i);
    }

    public int getChildrenNumber() {
        return children.size();
    }

    @SafeVarargs
    public static <T extends ItpMarker> ItpMarkerTree<T> Tree(final T marker,
                                                              final ItpMarkerTree<T>... subtrees) {
        return new ItpMarkerTree<>(marker, Arrays.asList(subtrees));
    }

    @SafeVarargs
    public static <T extends ItpMarker> ItpMarkerTree<T> Subtree(final T marker,
                                                                 final ItpMarkerTree<T>... subtrees) {
        return Tree(marker, subtrees);
    }

    public static <T extends ItpMarker> ItpMarkerTree<T> Leaf(final T marker) {
        return Tree(marker);
    }
}
