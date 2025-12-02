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
package hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl;

import com.koloboke.collect.map.IntObjMap;
import com.koloboke.collect.map.hash.HashIntObjMaps;
import com.koloboke.collect.map.hash.HashObjObjMaps;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.delta.collections.impl.MapUniqueTable;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import java.util.*;
import java.util.stream.Collectors;

public class OrNextStateDescriptor implements AbstractNextStateDescriptor {
    private static final UniqueTable<OrNextStateDescriptor> uniqueTable = new MapUniqueTable<>();

    public static void clearUniqueTable() {
        uniqueTable.clear();
    }

    private List<AbstractNextStateDescriptor> operands;

    private Map<Object, IntObjMapView<AbstractNextStateDescriptor>> diagonalCache =
            HashObjObjMaps.newUpdatableMap();

    // private IntObjMap<IntObjMapView<AbstractNextStateDescriptor>> offDiagonalCache =
    // HashIntObjMaps.newUpdatableMap();

    public static OrNextStateDescriptor create(final List<AbstractNextStateDescriptor> operands) {
        final ArrayList<AbstractNextStateDescriptor> ops = new ArrayList<>(operands);
        ops.sort(Comparator.comparingInt(Object::hashCode));

        return uniqueTable.checkIn(new OrNextStateDescriptor(ops));
    }

    private OrNextStateDescriptor(final List<AbstractNextStateDescriptor> operands) {
        this.operands = operands;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(
            final StateSpaceInfo localStateSpace) {
        class Diagonal implements IntObjMapView<AbstractNextStateDescriptor> {
            private final StateSpaceInfo localStateSpace;
            List<IntObjMapView<AbstractNextStateDescriptor>> diagonals = new ArrayList<>();

            private IntObjMap<AbstractNextStateDescriptor> cache = HashIntObjMaps.newUpdatableMap();
            private AbstractNextStateDescriptor defaultValue = null;

            Diagonal(List<AbstractNextStateDescriptor> operands, StateSpaceInfo localStateSpace) {
                this.localStateSpace = localStateSpace;
                for (AbstractNextStateDescriptor ns : operands) {
                    diagonals.add(ns.getDiagonal(localStateSpace));
                }
            }

            @Override
            public boolean isEmpty() {
                for (IntObjMapView<AbstractNextStateDescriptor> diagonal : diagonals) {
                    if (!diagonal.isEmpty()) {
                        return false;
                    }
                }
                return true;
            }

            @Override
            public boolean isProcedural() {
                return true;
            }

            @Override
            public boolean containsKey(final int key) {
                for (IntObjMapView<AbstractNextStateDescriptor> diagonal : diagonals) {
                    if (diagonal.containsKey(key)) {
                        return true;
                    }
                }
                return false;
            }

            @Override
            public AbstractNextStateDescriptor get(final int key) {
                AbstractNextStateDescriptor ret = cache.get(key);
                if (ret != null) {
                    return ret;
                }
                List<AbstractNextStateDescriptor> results = new ArrayList<>();
                for (IntObjMapView<AbstractNextStateDescriptor> diagonal : diagonals) {
                    final AbstractNextStateDescriptor value = diagonal.get(key);
                    if (!AbstractNextStateDescriptor.isNullOrEmpty(value)) {
                        results.add(value);
                    }
                }
                if (results.isEmpty()) {
                    ret = AbstractNextStateDescriptor.terminalEmpty();
                } else if (results.size() == 1) {
                    ret = results.get(0);
                } else {
                    ret = OrNextStateDescriptor.create(results);
                }

                cache.put(key, ret);
                return ret;
            }

            @Override
            public AbstractNextStateDescriptor defaultValue() {
                if (defaultValue != null) {
                    return defaultValue;
                }
                List<AbstractNextStateDescriptor> results = new ArrayList<>();
                for (IntObjMapView<AbstractNextStateDescriptor> diagonal : diagonals) {
                    final AbstractNextStateDescriptor value = diagonal.defaultValue();
                    if (!AbstractNextStateDescriptor.isNullOrEmpty(value)) {
                        results.add(value);
                    }
                }

                AbstractNextStateDescriptor ret;

                if (results.isEmpty()) {
                    ret = AbstractNextStateDescriptor.terminalEmpty();
                } else if (results.size() == 1) {
                    ret = results.get(0);
                } else {
                    ret = OrNextStateDescriptor.create(results);
                }
                defaultValue = ret;
                return ret;
            }

            @Override
            public IntObjCursor<? extends AbstractNextStateDescriptor> cursor() {
                // TODO: Auto-generated method stub.
                throw new UnsupportedOperationException("Not (yet) implemented.");
                // return 0;
            }

            @Override
            public int size() {
                // TODO: Auto-generated method stub.
                throw new UnsupportedOperationException("Not (yet) implemented.");
                // return 0;
            }
        }
        ;

        IntObjMapView<AbstractNextStateDescriptor> ret =
                diagonalCache.computeIfAbsent(
                        localStateSpace.getTraceInfo(),
                        (o) -> new Diagonal(operands, localStateSpace));

        return ret;
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            final StateSpaceInfo localStateSpace) {
        // TODO: Auto-generated method stub.
        throw new UnsupportedOperationException("Not (yet) implemented.");
        // return null;
    }

    @Override
    public Optional<Iterable<AbstractNextStateDescriptor>> split() {
        // TODO flatmap to handle hierarchical splitting
        return Optional.of(operands);
    }

    @Override
    public boolean equals(final Object o) {
        if (this == o) return true;
        if (!(o instanceof OrNextStateDescriptor)) return false;

        final OrNextStateDescriptor that = (OrNextStateDescriptor) o;

        return operands.equals(that.operands);
    }

    private int hashCode = 0;

    @Override
    public int hashCode() {
        if (hashCode != 0) {
            return hashCode;
        }
        return hashCode = operands.hashCode();
    }

    @Override
    public String toString() {
        return operands.stream().map(ns -> ns.toString()).collect(Collectors.joining(", "));
    }

    @Override
    public Cursor cursor(int from, StateSpaceInfo localStateSpace) {
        return AbstractNextStateDescriptor.super.cursor(from, localStateSpace);
    }

    @Override
    public Cursor rootCursor() {
        return RootOrCursor.of(
                operands.stream().map(AbstractNextStateDescriptor::rootCursor).toList());
    }

    public static class RootOrCursor implements AbstractNextStateDescriptor.Cursor {

        private final List<AbstractNextStateDescriptor.Cursor> cursors;

        private int currentPosition;

        private RootOrCursor(final List<Cursor> cursors) {
            this.cursors = cursors;
            this.currentPosition = -1;
        }

        public static AbstractNextStateDescriptor.Cursor of(final List<Cursor> cursors) {
            if (cursors.size() == 1) return cursors.get(0);
            else return new RootOrCursor(cursors);
        }

        @Override
        public int key() {
            throw new UnsupportedOperationException("Not (yet) implemented");
        }

        @Override
        public AbstractNextStateDescriptor value() {
            throw new UnsupportedOperationException("Not (yet) implemented");
        }

        @Override
        public boolean moveNext() {
            currentPosition++;
            this.cursors.forEach(AbstractNextStateDescriptor.Cursor::moveNext);
            return currentPosition == 0;
        }

        @Override
        public boolean moveTo(int key) {
            throw new UnsupportedOperationException("Not (yet) implemented");
        }

        @Override
        public Cursor valueCursor(int from, StateSpaceInfo localStateSpace) {
            return OrCursor.of(
                    cursors.stream().map(c -> c.valueCursor(from, localStateSpace)).toList());
        }

        @Override
        public void close() {
            cursors.forEach(AbstractNextStateDescriptor.Cursor::close);
        }

        @Override
        public Optional<Iterable<AbstractNextStateDescriptor.Cursor>> split() {
            return Optional.of(cursors);
        }
    }

    public static class OrCursor implements AbstractNextStateDescriptor.Cursor {

        private final List<AbstractNextStateDescriptor.Cursor> cursors;

        private List<AbstractNextStateDescriptor.Cursor> activeCursors;
        private Optional<Integer> key;

        private OrCursor(final List<AbstractNextStateDescriptor.Cursor> cursors) {
            this.cursors = cursors;
            this.activeCursors = new ArrayList<>();
            this.key = Optional.empty();
        }

        public static AbstractNextStateDescriptor.Cursor of(
                final List<AbstractNextStateDescriptor.Cursor> cursors) {
            if (cursors.size() == 1) return cursors.get(0);
            else return new OrCursor(cursors);
        }

        @Override
        public int key() {
            return key.orElseThrow();
        }

        @Override
        public AbstractNextStateDescriptor value() {
            AbstractNextStateDescriptor ret;

            if (activeCursors.isEmpty()) {
                ret = AbstractNextStateDescriptor.terminalEmpty();
            } else if (activeCursors.size() == 1) {
                ret = activeCursors.get(0).value();
            } else {
                ret =
                        OrNextStateDescriptor.create(
                                activeCursors.stream()
                                        .map(AbstractNextStateDescriptor.Cursor::value)
                                        .toList());
            }
            return ret;
        }

        @Override
        public boolean moveNext() {
            throw new UnsupportedOperationException("Not (yet) implemented");
        }

        @Override
        public boolean moveTo(int key) {
            boolean res = false;
            this.activeCursors = new ArrayList<>();
            for (AbstractNextStateDescriptor.Cursor cursor : cursors) {
                if (cursor.moveTo(key)) {
                    activeCursors.add(cursor);
                    res = true;
                }
            }
            if (res) {
                this.key = Optional.of(key);
            } else {
                this.key = Optional.empty();
            }
            return res;
        }

        @Override
        public AbstractNextStateDescriptor.Cursor valueCursor(
                int from, StateSpaceInfo localStateSpace) {
            return OrCursor.of(
                    activeCursors.stream().map(c -> c.valueCursor(from, localStateSpace)).toList());
        }

        @Override
        public void close() {
            cursors.forEach(AbstractNextStateDescriptor.Cursor::close);
        }

        @Override
        public Optional<Iterable<AbstractNextStateDescriptor.Cursor>> split() {
            return Optional.of(activeCursors);
        }
    }
}
