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
package hu.bme.mit.theta.solver.z3legacy;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpMarkerTree;
import hu.bme.mit.theta.solver.ItpPattern;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class Z3ItpPattern implements ItpPattern.Binary<Z3ItpMarker>,
        ItpPattern.Sequence<Z3ItpMarker>, ItpPattern.Tree<Z3ItpMarker> {

    final ItpMarkerTree<Z3ItpMarker> markerTree;

    Z3ItpPattern(final ItpMarkerTree<Z3ItpMarker> markerTree) {
        this.markerTree = markerTree;
    }

    @SuppressWarnings("unchecked")
    static Z3ItpPattern of(final ItpMarkerTree<? extends ItpMarker> markerTree) {
        final var list = new ArrayList<ItpMarkerTree<? extends ItpMarker>>();
        list.add(markerTree);
        while (!list.isEmpty()) {
            final var node = list.get(0);
            list.remove(0);

            checkArgument(node.getMarker() instanceof Z3ItpMarker);

            list.addAll(node.getChildren());
        }

        return new Z3ItpPattern((ItpMarkerTree<Z3ItpMarker>) markerTree);
    }

    @Override
    public Z3ItpMarker getA() {
        checkState(isBinary());
        return markerTree.getChild(0).getMarker();
    }

    @Override
    public Z3ItpMarker getB() {
        checkState(isBinary());
        return markerTree.getMarker();
    }

    @Override
    public List<Z3ItpMarker> getSequence() {
        checkState(isSequence());
        final var markerList = new ArrayList<Z3ItpMarker>();

        var current = markerTree;
        while (current.getChildrenNumber() > 0) {
            markerList.add(current.getMarker());
            current = current.getChild(0);
        }
        markerList.add(current.getMarker());

        return Lists.reverse(markerList);
    }

    @Override
    public ItpMarkerTree<Z3ItpMarker> getRoot() {
        return markerTree;
    }

    @Override
    public <E> E visit(ItpPatternVisitor<E> visitor) {
        return visitor.visitTreePattern(this);
    }

    private boolean isBinary() {
        return
                markerTree != null &&
                        markerTree.getChildrenNumber() == 1 &&
                        markerTree.getChild(0) != null &&
                        markerTree.getChild(0).getChildrenNumber() == 0;
    }

    private boolean isSequence() {
        var current = markerTree;
        while (current.getChildrenNumber() > 0) {
            if (current.getChildrenNumber() > 1) {
                return false;
            } else {
                current = current.getChild(0);
            }
        }
        return true;
    }
}
