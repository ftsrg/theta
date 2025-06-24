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
package hu.bme.mit.theta.analysis.algorithm.mdd.ansd;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.EmptyNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.IdentityNextStateDescriptor;
import java.io.Closeable;
import java.util.Optional;

public interface AbstractNextStateDescriptor {

    interface Precondition extends AbstractNextStateDescriptor {
        IntObjMapView<AbstractNextStateDescriptor> getValuations(StateSpaceInfo localStateSpace);

        @Override
        default boolean isNextStateDefined() {
            return false;
        }

        @Override
        default IntObjMapView<AbstractNextStateDescriptor> getDiagonal(
                StateSpaceInfo localStateSpace) {
            return getValuations(localStateSpace);
        }

        @Override
        default IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
                StateSpaceInfo localStateSpace) {
            // keep lambda to avoid confusion with overloads
            //noinspection Convert2MethodRef
            return new IntObjMapViews.Transforming<>(
                    getValuations(localStateSpace), v -> IntObjMapView.empty(v));
        }
    }

    interface Postcondition extends AbstractNextStateDescriptor {
        IntObjMapView<AbstractNextStateDescriptor> getValuations(StateSpaceInfo localStateSpace);

        @Override
        default boolean isSourceStateDefined() {
            return false;
        }

        @Override
        default IntObjMapView<AbstractNextStateDescriptor> getDiagonal(
                StateSpaceInfo localStateSpace) {
            return getValuations(localStateSpace);
        }

        @Override
        default IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
                StateSpaceInfo localStateSpace) {
            return IntObjMapView.empty(getValuations(localStateSpace));
        }

        final class TerminalEmpty implements AbstractNextStateDescriptor.Postcondition {
            @Override
            public IntObjMapView<AbstractNextStateDescriptor> getValuations(
                    StateSpaceInfo localStateSpace) {
                return IntObjMapView.empty(terminalEmpty());
            }

            @Override
            public Optional<Iterable<AbstractNextStateDescriptor>> split() {
                return Optional.empty();
            }

            @Override
            public boolean evaluate() {
                return false;
            }
        }

        TerminalEmpty TERMINAL_EMPTY = new TerminalEmpty();

        static AbstractNextStateDescriptor.Postcondition terminalEmpty() {
            return TERMINAL_EMPTY;
        }
    }

    static AbstractNextStateDescriptor terminalIdentity() {
        return IdentityNextStateDescriptor.TERMINAL_IDENTITY;
    }

    static AbstractNextStateDescriptor terminalEmpty() {
        return EmptyNextStateDescriptor.INSTANCE;
    }

    default boolean isSourceStateDefined() {
        return true;
    }

    default boolean isNextStateDefined() {
        return true;
    }

    IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace);

    IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace);

    default Optional<Iterable<AbstractNextStateDescriptor>> split() {
        return Optional.empty();
    }

    // Should return true only if there is a valuation that is accepted by the relation and false if
    // there is not.
    // Must throw an exception if undecidable.
    default boolean evaluate() {
        throw new IllegalStateException("Evaluated before reaching a terminal descriptor.");
    }

    default boolean isLocallyIdentity(final StateSpaceInfo stateSpaceInfo) {
        final IntObjMapView<AbstractNextStateDescriptor> diagonal = getDiagonal(stateSpaceInfo);
        final IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> offDiagonal =
                getOffDiagonal(stateSpaceInfo);
        final var res = offDiagonal.isEmpty()
                && isNullOrEmpty(offDiagonal.defaultValue())
                && diagonal.isEmpty();
        return res;
    }

    static boolean isNullOrEmpty(AbstractNextStateDescriptor ns) {
        return ns == null || ns == terminalEmpty();
    }

    static boolean isNullOrEmpty(IntObjMapView<? extends AbstractNextStateDescriptor> ns) {
        return ns == null || (ns.isEmpty() && isNullOrEmpty(ns.defaultValue()));
    }

    interface Cursor extends Closeable {

        int key();

        AbstractNextStateDescriptor value();

        boolean moveNext();

        boolean moveTo(int key);

        Cursor valueCursor(int from, StateSpaceInfo localStateSpace);

        void close();

        default Optional<Iterable<AbstractNextStateDescriptor.Cursor>> split() {
            return Optional.empty();
        }

        class Singleton implements Cursor {

            private final AbstractNextStateDescriptor value;

            private int currentPosition;

            public Singleton(AbstractNextStateDescriptor value) {
                this.value = value;
                this.currentPosition = -1;
            }

            @Override
            public int key() {
                return 0;
            }

            @Override
            public AbstractNextStateDescriptor value() {
                return value;
            }

            @Override
            public boolean moveNext() {
                currentPosition++;
                return currentPosition == 0;
            }

            @Override
            public boolean moveTo(int key) {
                return false;
            }

            @Override
            public Cursor valueCursor(int from, StateSpaceInfo localStateSpace) {
                return value.cursor(from, localStateSpace);
            }

            @Override
            public void close() {}
        }
    }

    default Cursor cursor(int from, StateSpaceInfo localStateSpace) {
        throw new UnsupportedOperationException("Not yet implemented");
    }

    default Cursor rootCursor() {
        return new Cursor.Singleton(this);
    }
}
