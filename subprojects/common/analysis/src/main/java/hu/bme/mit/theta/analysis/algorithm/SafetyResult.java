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

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.common.Utils;

import java.util.Optional;

import static com.google.common.base.Preconditions.checkNotNull;

public abstract class SafetyResult<S extends State, A extends Action> {

    private final Optional<ARG<S, A>> arg;
    private final Optional<Statistics> stats;

    private SafetyResult(final ARG<S, A> arg, final Optional<Statistics> stats) {
        this.arg = Optional.of(arg);
        this.stats = checkNotNull(stats);
    }

    private SafetyResult() {
        this.arg = Optional.empty();
        this.stats = Optional.empty();
    }


    public boolean hasArg() {
        return arg.isPresent();
    }

    public ARG<S, A> getArg() {
        return arg.orElseThrow();
    }

    public Optional<Statistics> getStats() {
        return stats;
    }

    // Factory methods

    public static <S extends State, A extends Action> Safe<S, A> safe(final ARG<S, A> arg,
                                                                      final Statistics stats) {
        return new Safe<>(arg, Optional.of(stats));
    }

    public static <S extends State, A extends Action> Safe<S, A> safe(final ARG<S, A> arg) {
        return new Safe<>(arg, Optional.empty());
    }

    public static <S extends State, A extends Action> Safe<S, A> safe() {
        return new Safe<>();
    }

    public static <S extends State, A extends Action> Unsafe<S, A> unsafe(final Trace<S, A> cex,
                                                                          final ARG<S, A> arg,
                                                                          final Statistics stats) {
        return new Unsafe<>(cex, arg, Optional.of(stats));
    }

    public static <S extends State, A extends Action> Unsafe<S, A> unsafe(final Trace<S, A> cex,
                                                                          final ARG<S, A> arg) {
        return new Unsafe<>(cex, arg, Optional.empty());
    }

    public static <S extends State, A extends Action> Unsafe<S, A> unsafe(final Trace<S, A> cex) {
        return new Unsafe<>(cex);
    }

    public static Unsafe<State, Action> unsafe() {
        return new Unsafe<>();
    }

    public static <S extends State, A extends Action> Unknown<S, A> unknown() {
        return new Unknown<>();
    }

    public abstract boolean isSafe();

    public abstract boolean isUnsafe();

    public abstract Safe<S, A> asSafe();

    public abstract Unsafe<S, A> asUnsafe();

    ////

    public static final class Safe<S extends State, A extends Action> extends SafetyResult<S, A> {

        private Safe(final ARG<S, A> arg, final Optional<Statistics> stats) {
            super(arg, stats);
        }

        private Safe() {
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
        public Safe<S, A> asSafe() {
            return this;
        }

        @Override
        public Unsafe<S, A> asUnsafe() {
            throw new ClassCastException(
                    "Cannot cast " + Safe.class.getSimpleName() + " to "
                            + Unsafe.class.getSimpleName());
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(SafetyResult.class.getSimpleName())
                    .add(Safe.class.getSimpleName())
                    .toString();
        }
    }

    public static final class Unsafe<S extends State, A extends Action> extends SafetyResult<S, A> {

        private final Optional<Trace<S, A>> cex;

        private Unsafe(final Trace<S, A> cex, final ARG<S, A> arg,
                       final Optional<Statistics> stats) {
            super(arg, stats);
            this.cex = Optional.of(cex);
        }

        private Unsafe(final Trace<S, A> cex) {
            this.cex = Optional.of(cex);
        }

        private Unsafe() {
            this.cex = Optional.empty();
        }

        public boolean hasTrace() {
            return cex.isPresent();
        }

        public Trace<S, A> getTrace() {
            return cex.orElseThrow();
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
        public Safe<S, A> asSafe() {
            throw new ClassCastException(
                    "Cannot cast " + Unsafe.class.getSimpleName() + " to "
                            + Safe.class.getSimpleName());
        }

        @Override
        public Unsafe<S, A> asUnsafe() {
            return this;
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(SafetyResult.class.getSimpleName())
                    .add(Unsafe.class.getSimpleName())
                    .add("Trace length: " + cex.map(Trace::length).orElse(-1)).toString();
        }
    }

    public static final class Unknown<S extends State, A extends Action> extends SafetyResult<S, A> {
        @Override
        public boolean isSafe() {
            return false;
        }

        @Override
        public boolean isUnsafe() {
            return false;
        }

        @Override
        public Safe<S, A> asSafe() {
            return null;
        }

        @Override
        public Unsafe<S, A> asUnsafe() {
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
