/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl;

import com.koloboke.collect.set.hash.HashIntSets;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import java.util.ArrayList;
import java.util.Objects;
import java.util.Optional;

/**
 * The intersection of two next-state relations, descended in lockstep. Operand shapes follow the
 * {@link AbstractNextStateDescriptor} algebra: a {@link AbstractNextStateDescriptor.Postcondition}
 * constrains the target only, a full relation constrains source and target, and a bound presented
 * over taller levels floats down the don't-care prefix itself (see {@link MddNodeNextStateDescriptor}
 * and {@link MddNodePostcondition} on a skipped-level handle). Enumeration drives the exhaustive
 * (no-default) side and probes the other by key, so pass the structural/explicit operand as {@code
 * lhs}.
 */
public final class AndNextStateDescriptor implements AbstractNextStateDescriptor {

    private final AbstractNextStateDescriptor lhs;

    private final AbstractNextStateDescriptor rhs;

    private AndNextStateDescriptor(AbstractNextStateDescriptor lhs, AbstractNextStateDescriptor rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    public static AbstractNextStateDescriptor of(
            AbstractNextStateDescriptor lhs, AbstractNextStateDescriptor rhs) {
        if (isEmptyDescriptor(lhs) || isEmptyDescriptor(rhs)) {
            return AbstractNextStateDescriptor.terminalEmpty();
        }
        if (lhs instanceof AbstractNextStateDescriptor.Postcondition l
                && rhs instanceof AbstractNextStateDescriptor.Postcondition r) {
            return of(l, r);
        }
        return new AndNextStateDescriptor(lhs, rhs);
    }

    /** Two postconditions AND into a postcondition (the init/prop initializer). */
    public static AbstractNextStateDescriptor.Postcondition of(
            AbstractNextStateDescriptor.Postcondition lhs,
            AbstractNextStateDescriptor.Postcondition rhs) {
        if (isEmptyDescriptor(lhs) || isEmptyDescriptor(rhs)) {
            return AbstractNextStateDescriptor.Postcondition.terminalEmpty();
        }
        return new AndPostcondition(lhs, rhs);
    }

    /** Both the plain and the Postcondition terminal-empty singletons count as empty. */
    private static boolean isEmptyDescriptor(AbstractNextStateDescriptor d) {
        return d == null
                || d == AbstractNextStateDescriptor.terminalEmpty()
                || d == AbstractNextStateDescriptor.Postcondition.terminalEmpty();
    }

    @Override
    public boolean isSourceStateDefined() {
        return lhs.isSourceStateDefined() || rhs.isSourceStateDefined();
    }

    @Override
    public boolean isNextStateDefined() {
        return lhs.isNextStateDefined() || rhs.isNextStateDefined();
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        return andViews(lhs.getDiagonal(localStateSpace), rhs.getDiagonal(localStateSpace));
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace) {
        final IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> l =
                lhs.getOffDiagonal(localStateSpace);
        final IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> r =
                rhs.getOffDiagonal(localStateSpace);
        return new IntObjMapView<>() {
            @Override
            public IntObjMapView<AbstractNextStateDescriptor> get(int source) {
                final IntObjMapView<AbstractNextStateDescriptor> li = childOr(l, source);
                final IntObjMapView<AbstractNextStateDescriptor> ri = childOr(r, source);
                if (li == null || ri == null) {
                    return IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty());
                }
                return andViews(li, ri);
            }

            @Override
            public IntObjMapView<AbstractNextStateDescriptor> defaultValue() {
                if (l.defaultValue() == null || r.defaultValue() == null) return null;
                return andViews(l.defaultValue(), r.defaultValue());
            }

            @Override
            public IntObjCursor<? extends IntObjMapView<AbstractNextStateDescriptor>> cursor() {
                return mapCursor(l, r, this::get);
            }

            @Override
            public boolean isEmpty() {
                return (l.isEmpty() && l.defaultValue() == null)
                        || (r.isEmpty() && r.defaultValue() == null);
            }

            @Override
            public boolean isProcedural() {
                return l.isProcedural() || r.isProcedural();
            }

            @Override
            public boolean containsKey(int key) {
                return (l.containsKey(key) || l.defaultValue() != null)
                        && (r.containsKey(key) || r.defaultValue() != null);
            }

            @Override
            public int size() {
                throw new UnsupportedOperationException();
            }
        };
    }

    /** Intersects two target views, descending each key to {@code of} of the children. */
    private static IntObjMapView<AbstractNextStateDescriptor> andViews(
            IntObjMapView<AbstractNextStateDescriptor> l, IntObjMapView<AbstractNextStateDescriptor> r) {
        return new IntObjMapView<>() {
            @Override
            public AbstractNextStateDescriptor get(int key) {
                final AbstractNextStateDescriptor a = childOr(l, key);
                final AbstractNextStateDescriptor b = childOr(r, key);
                if (a == null || b == null) return AbstractNextStateDescriptor.terminalEmpty();
                return AndNextStateDescriptor.of(a, b);
            }

            @Override
            public AbstractNextStateDescriptor defaultValue() {
                if (l.defaultValue() == null || r.defaultValue() == null) return null;
                return AndNextStateDescriptor.of(l.defaultValue(), r.defaultValue());
            }

            @Override
            public IntObjCursor<? extends AbstractNextStateDescriptor> cursor() {
                // drive by cursor value (not get), so a cursor-only operand (the reversed CTL
                // relation) can drive; both-default falls back to the key-union mapCursor
                if (isEmptyValue(l.defaultValue())) return driveCursor(l, r, true);
                if (isEmptyValue(r.defaultValue())) return driveCursor(r, l, false);
                return mapCursor(l, r, this::get);
            }

            @Override
            public boolean isEmpty() {
                return (l.isEmpty() && l.defaultValue() == null)
                        || (r.isEmpty() && r.defaultValue() == null);
            }

            @Override
            public boolean isProcedural() {
                // procedural iff the driven (no-default) side is; a bounded driver makes the result
                // explicit even over a procedural other side, which is only probed
                if (isEmptyValue(l.defaultValue())) return l.isProcedural();
                if (isEmptyValue(r.defaultValue())) return r.isProcedural();
                return l.isProcedural() || r.isProcedural();
            }

            @Override
            public boolean containsKey(int key) {
                return (l.containsKey(key) || l.defaultValue() != null)
                        && (r.containsKey(key) || r.defaultValue() != null);
            }

            @Override
            public int size() {
                int n = 0;
                for (var c = cursor(); c.moveNext(); ) n++;
                return n;
            }
        };
    }

    private static <V> V childOr(IntObjMapView<V> view, int key) {
        final V child = view.get(key);
        return child != null ? child : view.defaultValue();
    }

    /** ANDs [driver]'s cursor values with [other]'s child by key, keeping operand order; never gets [driver]. */
    private static IntObjCursor<AbstractNextStateDescriptor> driveCursor(
            IntObjMapView<AbstractNextStateDescriptor> driver,
            IntObjMapView<AbstractNextStateDescriptor> other,
            boolean driverIsLeft) {
        final var dc = driver.cursor();
        return new IntObjCursor<>() {
            private AbstractNextStateDescriptor value;

            @Override
            public int key() {
                return dc.key();
            }

            @Override
            public AbstractNextStateDescriptor value() {
                return value;
            }

            @Override
            public boolean moveNext() {
                while (dc.moveNext()) {
                    final AbstractNextStateDescriptor o = childOr(other, dc.key());
                    if (o == null) continue;
                    final AbstractNextStateDescriptor combined =
                            driverIsLeft ? of(dc.value(), o) : of(o, dc.value());
                    if (!isEmptyValue(combined)) {
                        value = combined;
                        return true;
                    }
                }
                return false;
            }
        };
    }

    /** Like {@link #driveCursor} but recomputes values via [valueOf]; unions both key sets when both default. */
    private static <V> IntObjCursor<V> mapCursor(
            IntObjMapView<?> l, IntObjMapView<?> r, java.util.function.IntFunction<V> valueOf) {
        final var keys = new ArrayList<Integer>();
        if (isEmptyValue(l.defaultValue())) {
            for (var c = l.cursor(); c.moveNext(); ) keys.add(c.key());
        } else if (isEmptyValue(r.defaultValue())) {
            for (var c = r.cursor(); c.moveNext(); ) keys.add(c.key());
        } else {
            final var seen = HashIntSets.newMutableSet();
            for (var c = l.cursor(); c.moveNext(); ) {
                keys.add(c.key());
                seen.add(c.key());
            }
            for (var c = r.cursor(); c.moveNext(); ) {
                if (!seen.contains(c.key())) keys.add(c.key());
            }
        }
        return new IntObjCursor<>() {
            private int index = -1;
            private int key;
            private V value;

            @Override
            public int key() {
                return key;
            }

            @Override
            public V value() {
                return value;
            }

            @Override
            public boolean moveNext() {
                while (++index < keys.size()) {
                    final int k = keys.get(index);
                    final V v = valueOf.apply(k);
                    if (!isEmptyValue(v)) {
                        key = k;
                        value = v;
                        return true;
                    }
                }
                return false;
            }
        };
    }

    private static boolean isEmptyValue(Object v) {
        if (v == null) return true;
        if (v instanceof AbstractNextStateDescriptor d) return isEmptyDescriptor(d);
        if (v instanceof IntObjMapView<?> view) {
            return view.isEmpty() && view.defaultValue() == null;
        }
        return false;
    }

    @Override
    public Optional<Iterable<AbstractNextStateDescriptor>> split() {
        // only the relation splits (disjunctive partitioning); re-wrap keeping operand order
        if (lhs.split().isPresent()) {
            return lhs.split()
                    .map(
                            iterable -> {
                                final var list = new ArrayList<AbstractNextStateDescriptor>();
                                iterable.forEach(it -> list.add(of(it, rhs)));
                                return list;
                            });
        }
        if (rhs.split().isPresent()) {
            return rhs.split()
                    .map(
                            iterable -> {
                                final var list = new ArrayList<AbstractNextStateDescriptor>();
                                iterable.forEach(it -> list.add(of(lhs, it)));
                                return list;
                            });
        }
        return Optional.empty();
    }

    // isLocallyIdentity uses the interface default (inspects the intersected diagonal/off-diagonal),
    // correct whether an operand is identity or a don't-care prefix leaves the other constraining.

    @Override
    public boolean evaluate() {
        return lhs.evaluate() && rhs.evaluate();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        AndNextStateDescriptor that = (AndNextStateDescriptor) o;
        return Objects.equals(lhs, that.lhs) && Objects.equals(rhs, that.rhs);
    }

    @Override
    public int hashCode() {
        return Objects.hash(lhs, rhs);
    }

    @Override
    public String toString() {
        return "And(" + lhs + ", " + rhs + ")";
    }

    /** The intersection of two postconditions, as a postcondition (the init/prop initializer). */
    static final class AndPostcondition implements AbstractNextStateDescriptor.Postcondition {

        private final AbstractNextStateDescriptor.Postcondition lhs;

        private final AbstractNextStateDescriptor.Postcondition rhs;

        private AndPostcondition(
                AbstractNextStateDescriptor.Postcondition lhs,
                AbstractNextStateDescriptor.Postcondition rhs) {
            this.lhs = lhs;
            this.rhs = rhs;
        }

        @Override
        public IntObjMapView<AbstractNextStateDescriptor> getValuations(
                StateSpaceInfo localStateSpace) {
            return andViews(lhs.getValuations(localStateSpace), rhs.getValuations(localStateSpace));
        }

        @Override
        public boolean evaluate() {
            return lhs.evaluate() && rhs.evaluate();
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            AndPostcondition that = (AndPostcondition) o;
            return Objects.equals(lhs, that.lhs) && Objects.equals(rhs, that.rhs);
        }

        @Override
        public int hashCode() {
            return Objects.hash(lhs, rhs);
        }

        @Override
        public String toString() {
            return "AndPost(" + lhs + ", " + rhs + ")";
        }
    }
}
