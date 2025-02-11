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
package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Cex;
import hu.bme.mit.theta.common.Utils;
import java.util.Optional;

public abstract class SafetyResult<Pr extends Proof, C extends Cex> implements Result<Pr> {
    private final Pr proof;
    private final Optional<Statistics> stats;

    private SafetyResult(final Pr proof, final Optional<Statistics> stats) {
        this.proof = checkNotNull(proof);
        this.stats = checkNotNull(stats);
    }

    private SafetyResult() {
        this.proof = null;
        this.stats = Optional.empty();
    }

    @Override
    public Pr getProof() {
        return proof;
    }

    @Override
    public Optional<Statistics> getStats() {
        return stats;
    }

    public static <Pr extends Proof, C extends Cex> Safe<Pr, C> safe(final Pr witness) {
        return new Safe<>(witness, Optional.empty());
    }

    public static <Pr extends Proof, C extends Cex> Unsafe<Pr, C> unsafe(
            final C cex, final Pr witness) {
        return new Unsafe<>(cex, witness, Optional.empty());
    }

    public static <Pr extends Proof, C extends Cex> Unknown<Pr, C> unknown() {
        return new Unknown<>();
    }

    public static <Pr extends Proof, C extends Cex> Safe<Pr, C> safe(
            final Pr witness, final Statistics stats) {
        return new Safe<>(witness, Optional.of(stats));
    }

    public static <Pr extends Proof, C extends Cex> Unsafe<Pr, C> unsafe(
            final C cex, final Pr witness, final Statistics stats) {
        return new Unsafe<>(cex, witness, Optional.of(stats));
    }

    public static <Pr extends Proof, C extends Cex> Unknown<Pr, C> unknown(final Statistics stats) {
        return new Unknown<>(Optional.of(stats));
    }

    public abstract boolean isSafe();

    public abstract boolean isUnsafe();

    public abstract Safe<Pr, C> asSafe();

    public abstract Unsafe<Pr, C> asUnsafe();

    ////

    public static final class Safe<Pr extends Proof, C extends Cex> extends SafetyResult<Pr, C> {
        private Safe(final Pr proof, final Optional<Statistics> stats) {
            super(proof, stats);
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
        public Safe<Pr, C> asSafe() {
            return this;
        }

        @Override
        public Unsafe<Pr, C> asUnsafe() {
            throw new ClassCastException(
                    "Cannot cast "
                            + Safe.class.getSimpleName()
                            + " to "
                            + Unsafe.class.getSimpleName());
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(SafetyResult.class.getSimpleName())
                    .add(Safe.class.getSimpleName())
                    .toString();
        }
    }

    public static final class Unsafe<Pr extends Proof, C extends Cex> extends SafetyResult<Pr, C> {
        private final C cex;

        private Unsafe(final C cex, final Pr proof, final Optional<Statistics> stats) {
            super(proof, stats);
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
        public Safe<Pr, C> asSafe() {
            throw new ClassCastException(
                    "Cannot cast "
                            + Unsafe.class.getSimpleName()
                            + " to "
                            + Safe.class.getSimpleName());
        }

        @Override
        public Unsafe<Pr, C> asUnsafe() {
            return this;
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(SafetyResult.class.getSimpleName())
                    .add(Unsafe.class.getSimpleName())
                    .add("Trace length: " + cex.length())
                    .toString();
        }
    }

    public static final class Unknown<Pr extends Proof, C extends Cex> extends SafetyResult<Pr, C> {

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
        public Safe<Pr, C> asSafe() {
            return null;
        }

        @Override
        public Unsafe<Pr, C> asUnsafe() {
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
