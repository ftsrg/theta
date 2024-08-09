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
package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.Cex;
import hu.bme.mit.theta.common.Utils;

import java.util.Optional;

import static com.google.common.base.Preconditions.checkNotNull;

public abstract class SafetyResult<W extends Witness, C extends Cex> implements Result<W> {
    private final W witness;
    private final Optional<Statistics> stats;

    private SafetyResult(final W witness, final Optional<Statistics> stats) {
        this.witness = checkNotNull(witness);
        this.stats = checkNotNull(stats);
    }

    private SafetyResult() {
        this.witness = null;
        this.stats = Optional.empty();
    }

    @Override
    public W getWitness() {
        return witness;
    }

    @Override
    public Optional<Statistics> getStats() {
        return stats;
    }

    public static <W extends Witness, C extends Cex> Safe<W, C> safe(final W witness) {
        return new Safe<>(witness, Optional.empty());
    }

    public static <W extends Witness, C extends Cex> Unsafe<W, C> unsafe(final C cex, final W witness) {
        return new Unsafe<>(cex, witness, Optional.empty());
    }

    public static <W extends Witness, C extends Cex> Unknown<W, C> unknown() {
        return new Unknown<>();
    }

    public static <W extends Witness, C extends Cex> Safe<W, C> safe(final W witness, final Statistics stats) {
        return new Safe<>(witness, Optional.of(stats));
    }

    public static <W extends Witness, C extends Cex> Unsafe<W, C> unsafe(final C cex, final W witness,
                                                                         final Statistics stats) {
        return new Unsafe<>(cex, witness, Optional.of(stats));
    }

    public static <W extends Witness, C extends Cex> Unknown<W, C> unknown(final Statistics stats) {
        return new Unknown<>(Optional.of(stats));
    }

    public abstract boolean isSafe();

    public abstract boolean isUnsafe();

    public abstract Safe<W, C> asSafe();

    public abstract Unsafe<W, C> asUnsafe();

    ////

    public static final class Safe<W extends Witness, C extends Cex> extends SafetyResult<W, C> {
        private Safe(final W witness, final Optional<Statistics> stats) {
            super(witness, stats);
        }

        @Override
        public boolean isSafe() {
            return true;
        }

        @Override
        public boolean isUnsafe() {
            return false;
        }

        @Override
        public Safe<W, C> asSafe() {
            return this;
        }

        @Override
        public Unsafe<W, C> asUnsafe() {
            throw new ClassCastException(
                    "Cannot cast " + Safe.class.getSimpleName() + " to " + Unsafe.class.getSimpleName());
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(SafetyResult.class.getSimpleName()).add(Safe.class.getSimpleName())
                    .toString();
        }
    }

    public static final class Unsafe<W extends Witness, C extends Cex> extends SafetyResult<W, C> {
        private final C cex;

        private Unsafe(final C cex, final W witness, final Optional<Statistics> stats) {
            super(witness, stats);
            this.cex = checkNotNull(cex);
        }

        public C getCex() {
            return cex;
        }

        @Override
        public boolean isSafe() {
            return false;
        }

        @Override
        public boolean isUnsafe() {
            return true;
        }

        @Override
        public Safe<W, C> asSafe() {
            throw new ClassCastException(
                    "Cannot cast " + Unsafe.class.getSimpleName() + " to " + Safe.class.getSimpleName());
        }

        @Override
        public Unsafe<W, C> asUnsafe() {
            return this;
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(SafetyResult.class.getSimpleName()).add(Unsafe.class.getSimpleName())
                    .add("Trace length: " + cex.length()).toString();
        }
    }

    public static final class Unknown<W extends Witness, C extends Cex> extends SafetyResult<W, C> {

        public Unknown() {
            super();
        }

        public Unknown(final Optional<Statistics> stats) {
            super(null, stats);
        }

        @Override
        public boolean isSafe() {
            return false;
        }

        @Override
        public boolean isUnsafe() {
            return false;
        }

        @Override
        public Safe<W, C> asSafe() {
            return null;
        }

        @Override
        public Unsafe<W, C> asUnsafe() {
            return null;
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(SafetyResult.class.getSimpleName())
                    .add(Unknown.class.getSimpleName())
                    .toString();
        }
    }

}
