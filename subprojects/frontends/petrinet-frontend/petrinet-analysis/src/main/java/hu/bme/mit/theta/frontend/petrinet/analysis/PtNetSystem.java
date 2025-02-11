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

import com.google.common.collect.ImmutableBiMap;
import com.koloboke.collect.map.ObjIntMap;
import com.koloboke.collect.map.hash.HashObjIntMaps;
import com.koloboke.collect.map.hash.HashObjObjMap;
import com.koloboke.collect.map.hash.HashObjObjMaps;
import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.delta.collections.impl.MapUniqueTable;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OrNextStateDescriptor;
import hu.bme.mit.theta.frontend.petrinet.model.*;
import java.awt.*;
import java.awt.image.BufferedImage;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;

public final class PtNetSystem {
    public static class TransitionEffect {
        public static final TransitionEffect INDEPENDENT =
                new TransitionEffect(0, Integer.MAX_VALUE, 0);

        public final int takes;
        public final int inhibits;
        public final int puts;

        public TransitionEffect(final int takes, final int inhibits, final int puts) {
            this.takes = takes;
            this.inhibits = inhibits;
            this.puts = puts;
        }

        public boolean isDependent() {
            return takes != 0 || puts != 0 || inhibits != Integer.MAX_VALUE;
        }

        public boolean reads() {
            return inhibits != Integer.MAX_VALUE || (takes == puts && takes > 0);
        }

        public boolean writes() {
            return takes != puts;
        }

        public String toString() {
            if (writes()) {
                return "rw";
            } else if (reads()) {
                return "r";
            } else {
                return "";
            }
        }
    }

    private PetriNet petriNet;
    private final List<Place> placeOrdering;

    private Map<Transition, Map<Place, TransitionEffect>> dependencyMatrix =
            HashObjObjMaps.newUpdatableMap();
    private ObjIntMap<Transition> transitionTop = HashObjIntMaps.newUpdatableMap();
    boolean hasReadOnlyEffect = false;
    boolean hasReadOnlyEffectOnTop = false;

    private AbstractNextStateDescriptor.Postcondition initializer;
    private AbstractNextStateDescriptor transitions;

    public PtNetSystem(final PetriNet petriNet, List<Place> placeOrdering) {
        if (petriNet.getPlaces().size() != placeOrdering.size()) {
            throw new IllegalArgumentException();
        }
        if (placeOrdering.isEmpty()) {
            throw new IllegalArgumentException();
        }
        this.petriNet = petriNet;
        this.placeOrdering = placeOrdering;
        initializer = createInitializer();
        transitions = createTransitions();

        for (Place p : petriNet.getPlaces()) {
            if (!placeOrdering.contains(p)) {
                throw new IllegalArgumentException("Ordering does not contain place " + p.getId());
            }
        }
    }

    private AbstractNextStateDescriptor.Postcondition createInitializer() {
        PtNetInitializer current =
                new PtNetInitializer(
                        placeOrdering.get(0),
                        Math.toIntExact(placeOrdering.get(0).getInitialMarking()),
                        AbstractNextStateDescriptor.terminalIdentity());
        for (int i = 1; i < placeOrdering.size(); ++i) {
            current =
                    new PtNetInitializer(
                            placeOrdering.get(i),
                            Math.toIntExact(placeOrdering.get(i).getInitialMarking()),
                            current);
        }
        return current;
    }

    private AbstractNextStateDescriptor createTransitions() {
        List<AbstractNextStateDescriptor> descriptors = new ArrayList<>();
        UniqueTable<AbstractNextStateDescriptor> uniqueTable = new MapUniqueTable<>();
        for (Transition t : petriNet.getTransitions()) {
            descriptors.add(createTransition(t, uniqueTable));
        }
        return OrNextStateDescriptor.create(descriptors);
    }

    private AbstractNextStateDescriptor createTransition(
            final Transition t, final UniqueTable<AbstractNextStateDescriptor> uniqueTable) {
        ObjIntMap<Place> takes = HashObjIntMaps.newUpdatableMap(t.getIncomingArcs().size());
        ObjIntMap<Place> puts = HashObjIntMaps.newUpdatableMap(t.getOutgoingArcs().size());
        ObjIntMap<Place> inhibits = HashObjIntMaps.newUpdatableMap();

        for (PTArc arc : t.getIncomingArcs()) {
            if (arc.isInhibitor()) {
                inhibits.put(arc.getSource(), Math.toIntExact(arc.getWeight()));
            } else {
                takes.put(arc.getSource(), Math.toIntExact(arc.getWeight()));
            }
        }
        for (TPArc arc : t.getOutgoingArcs()) {
            puts.put(arc.getTarget(), Math.toIntExact(arc.getWeight()));
        }

        final HashObjObjMap<Place, TransitionEffect> transitionDependecies =
                HashObjObjMaps.newUpdatableMap();

        boolean readOnlyOnTop = false;

        AbstractNextStateDescriptor current = AbstractNextStateDescriptor.terminalIdentity();
        for (int i = 0; i < placeOrdering.size(); ++i) {
            final int nTakes = takes.getOrDefault(placeOrdering.get(i), 0);
            final int nInhibits = inhibits.getOrDefault(placeOrdering.get(i), Integer.MAX_VALUE);
            final int nPuts = puts.getOrDefault(placeOrdering.get(i), 0);

            if (nTakes != 0 || nPuts != 0 || nInhibits != Integer.MAX_VALUE) {
                final TransitionEffect effect = new TransitionEffect(nTakes, nInhibits, nPuts);
                transitionDependecies.put(placeOrdering.get(i), effect);
                transitionTop.put(t, i);

                if (effect.reads() && !effect.writes()) {
                    hasReadOnlyEffect = true;
                    readOnlyOnTop = true;
                } else {
                    readOnlyOnTop = false;
                }

                current =
                        uniqueTable.checkIn(
                                new PtNetTransitionNextStateDescriptor(
                                        t,
                                        placeOrdering.get(i),
                                        nTakes,
                                        nInhibits,
                                        nPuts,
                                        current));
            }
        }

        hasReadOnlyEffectOnTop = hasReadOnlyEffectOnTop || readOnlyOnTop;

        dependencyMatrix.put(t, transitionDependecies);

        return current;
    }

    public AbstractNextStateDescriptor.Postcondition getInitializer() {
        return initializer;
    }

    public AbstractNextStateDescriptor getTransitions() {
        return transitions;
    }

    public String printDependencyMatrixCsv() {
        StringBuilder sb = new StringBuilder();
        for (Place p : placeOrdering) {
            sb.append(';');
            sb.append('"');
            sb.append(p.getId());
            sb.append('"');
        }
        sb.append('\n');
        List<String> transitionLines = new ArrayList<>(getTransitionCount());
        for (Transition t : petriNet.getTransitions()) {
            StringBuilder sb2 = new StringBuilder();
            sb2.append('"');
            sb2.append(t.getId());
            sb2.append('"');

            for (Place p : placeOrdering) {
                sb2.append(';');
                sb2.append(
                        dependencyMatrix
                                .getOrDefault(t, Map.of())
                                .getOrDefault(p, TransitionEffect.INDEPENDENT)
                                .toString());
            }
            sb2.append('\n');
            transitionLines.add(sb2.toString());
        }

        transitionLines.sort(
                (a, b) ->
                        String.CASE_INSENSITIVE_ORDER.compare(reverseString(a), reverseString(b)));

        for (String line : transitionLines) {
            sb.append(line);
        }

        return sb.toString();
    }

    public static String reverseString(String str) {
        StringBuilder sb = new StringBuilder(str);
        sb.reverse();
        return sb.toString();
    }

    public BufferedImage dependencyMatrixImage(final int blockWidth) {
        int width = placeOrdering.size() * blockWidth,
                height = petriNet.getTransitions().size() * blockWidth;

        // TYPE_INT_ARGB specifies the image format: 8-bit RGBA packed
        // into integer pixels
        BufferedImage bi = new BufferedImage(width, height, BufferedImage.TYPE_INT_ARGB);

        Graphics2D graphics = bi.createGraphics();

        final List<Transition> transitions = new ArrayList<>(petriNet.getTransitions());
        transitions.sort(Comparator.comparingInt(t -> transitionTop.getOrDefault(t, -1)));
        for (int y = 0; y < transitions.size(); y++) {
            final Transition t = transitions.get(y);

            for (int x = 0; x < placeOrdering.size(); x++) {
                final Place p = placeOrdering.get(x);
                final TransitionEffect effect =
                        dependencyMatrix
                                .getOrDefault(t, Map.of())
                                .getOrDefault(p, TransitionEffect.INDEPENDENT);

                if (effect.writes()) {
                    graphics.setPaint(Color.RED);
                } else if (effect.reads()) {
                    graphics.setPaint(Color.GREEN);
                } else {
                    graphics.setPaint(Color.WHITE);
                }

                graphics.fillRect(x * blockWidth, y * blockWidth, blockWidth, blockWidth);
                // graphics.setPaint(Color.LIGHT_GRAY);
                // graphics.drawRect(x*blockWidth, y*blockWidth, blockWidth + 1, blockWidth + 1);
            }
        }

        return bi;
    }

    public String getName() {
        return petriNet.getName() == null ? petriNet.getId() : petriNet.getName();
    }

    public boolean hasReadOnlyEffect() {
        return hasReadOnlyEffect;
    }

    public boolean hasReadOnlyEffectOnTop() {
        return hasReadOnlyEffectOnTop;
    }

    public int getPlaceCount() {
        return petriNet.getPlaces().size();
    }

    public int getTransitionCount() {
        return petriNet.getTransitions().size();
    }

    public int getArcCount() {
        return petriNet.getPtArcs().size() + petriNet.getTpArcs().size();
    }

    public Map<Transition, Map<Place, TransitionEffect>> getDependencyMatrix() {
        return ImmutableBiMap.copyOf(dependencyMatrix);
    }

    public PetriNet getPetriNet() {
        return petriNet;
    }
}
