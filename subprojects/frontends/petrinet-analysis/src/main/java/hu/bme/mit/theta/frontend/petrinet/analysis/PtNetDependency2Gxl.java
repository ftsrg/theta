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
package hu.bme.mit.theta.frontend.petrinet.analysis;

import com.koloboke.collect.set.hash.HashObjSets;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import hu.bme.mit.theta.frontend.petrinet.model.Transition;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public final class PtNetDependency2Gxl {
    private static final int K = 100;

    private static class DepEdge {
        public final PlaceRef a;
        public final PlaceRef b;
        public final int weight;

        private DepEdge(final PlaceRef a, final PlaceRef b) {
            this(a, b, 1);
            // this.a = a.getId().compareTo(b.getId()) < 0 ? a : b;
            // this.b = a.getId().compareTo(b.getId()) < 0 ? b : a;
        }

        private DepEdge(final PlaceRef a, final PlaceRef b, int weight) {
            this.a = a;
            this.b = b;
            this.weight = weight;
        }

        @Override
        public boolean equals(final Object o) {
            if (this == o) return true;
            if (!(o instanceof DepEdge)) return false;

            final DepEdge depEdge = (DepEdge) o;

            if (!a.equals(depEdge.a)) return false;
            if (weight != depEdge.weight) return false;
            return b.equals(depEdge.b);
        }

        @Override
        public int hashCode() {
            int result = a.hashCode();
            result = 31 * result + b.hashCode();
            result = 31 * result + weight;
            return result;
        }
    }

    private static class PlaceRef {
        private final Place ref;
        private final String id;

        private PlaceRef(String id) {
            this.ref = null;
            this.id = id;
        }

        private PlaceRef(final Place ref) {
            this.ref = ref;
            this.id = ref.getId();
        }

        @Override
        public int hashCode() {
            return ref == null ? id.hashCode() : ref.hashCode();
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) return true;
            if (obj instanceof PlaceRef) {
                PlaceRef other = (PlaceRef) obj;
                return Objects.equals(ref, other.ref) && Objects.equals(id, other.id);
            }
            return false;
        }

        private String getId() {
            return id;
        }
    }

    public static String toGxl(PtNetSystem system, final boolean omitReadOnly) {
        final Map<Transition, Map<Place, PtNetSystem.TransitionEffect>> depMat =
                system.getDependencyMatrix();

        Set<PlaceRef> nodes = HashObjSets.newUpdatableSet();
        Set<DepEdge> edges = HashObjSets.newUpdatableSet();
        // if (omitReadOnly) {
        // 	PlaceRef rootNode = new PlaceRef("_______aux_");
        // 	nodes.add(rootNode);
        // 	for (Place p : system.getPetriNet().getPlaces()) {
        // 		final PlaceRef pRef = new PlaceRef(p);
        // 		nodes.add(pRef);
        // 		edges.add(new DepEdge(rootNode, pRef, system.getPlaceCount()));
        // 	}
        // } else {
        for (Place p : system.getPetriNet().getPlaces()) {
            final PlaceRef pRef = new PlaceRef(p);
            nodes.add(pRef);
        }
        // }

        for (Map.Entry<Transition, Map<Place, PtNetSystem.TransitionEffect>> t :
                depMat.entrySet()) {
            Set<Place> inPlaces = HashObjSets.newUpdatableSet();
            Set<Place> outPlaces = HashObjSets.newUpdatableSet();
            // Set<Place> readOnlyPlaces = HashObjSets.newUpdatableSet();
            for (Map.Entry<Place, PtNetSystem.TransitionEffect> e : t.getValue().entrySet()) {
                if (e.getValue().takes == e.getValue().puts) {
                    // readOnlyPlaces.add(e.getKey());
                    if (omitReadOnly) {
                        continue;
                    }
                }
                if (e.getValue().takes > 0 || e.getValue().inhibits < Integer.MAX_VALUE) {
                    inPlaces.add(e.getKey());
                }
                if (e.getValue().puts > 0) {
                    outPlaces.add(e.getKey());
                }
            }

            if (t.getValue().size() > K) {
                PlaceRef transitionNode = new PlaceRef("_______aux_" + t.getKey().getId());
                nodes.add(transitionNode);

                for (Place p : inPlaces) {
                    edges.add(new DepEdge(new PlaceRef(p), transitionNode));
                }

                for (Place p : outPlaces) {
                    edges.add(new DepEdge(new PlaceRef(p), transitionNode));
                }
            } else {
                for (Place p1 : inPlaces) {
                    for (Place p2 : outPlaces) {
                        edges.add(new DepEdge(new PlaceRef(p1), new PlaceRef(p2)));
                    }
                }
            }
        }

        return serializeGxl(system.getPetriNet().getName(), nodes, edges);
    }

    private static String serializeGxl(
            final String name, final Set<PlaceRef> nodes, final Set<DepEdge> edges) {
        StringBuilder sb = new StringBuilder();
        sb.append("<gxl>\n");
        sb.append("<graph id=\"" + name + "\" edgemode=\"defaultdirected\">\n");

        for (PlaceRef node : nodes) {
            sb.append("<node id=\"" + node.getId() + "\"/>\n");
        }

        for (DepEdge edge : edges) {
            // if (edge.weight == 1) {
            sb.append(
                    "<edge id=\""
                            + edge.a.getId()
                            + "_"
                            + edge.b.getId()
                            + "\" from=\""
                            + edge.a.getId()
                            + "\" "
                            + "to=\""
                            + edge.b.getId()
                            + "\" isdirected=\"true\" />\n");
            // } else {
            // sb.append("<edge id=\"")
            // 	.append(edge.a.getId())
            // 	.append("_")
            // 	.append(edge.b.getId())
            // 	.append("\" from=\"")
            // 	.append(edge.a.getId())
            // 	.append("\" ")
            // 	.append("to=\"")
            // 	.append(edge.b.getId())
            // 	.append("\" isdirected=\"true\">\n")
            // 	.append("<attr name=\"weight\">\n" + "<int>")
            // 	.append(edge.weight)
            // 	.append("</int>\n")
            // 	.append("</attr></edge>");
            // }
        }

        sb.append("</graph>\n");
        sb.append("</gxl>\n");

        return sb.toString();
    }
}
