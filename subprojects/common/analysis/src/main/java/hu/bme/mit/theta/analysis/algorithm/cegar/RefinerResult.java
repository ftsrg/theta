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
package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Cex;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.Utils;

/**
 * Represents the result of the Refiner class that can be either spurious or unsafe. In the former
 * case it also contains the refined precision and in the latter case the feasible counterexample.
 */
public abstract class RefinerResult<P extends Prec, C extends Cex> {

    protected RefinerResult() {}

    /**
     * Create a new spurious result.
     *
     * @param refinedPrec Refined precision
     */
    public static <P extends Prec, C extends Cex> Spurious<P, C> spurious(final P refinedPrec) {
        return new Spurious<>(refinedPrec);
    }

    /**
     * Creates a new unsafe result.
     *
     * @param cex Feasible counterexample
     */
    public static <P extends Prec, C extends Cex> Unsafe<P, C> unsafe(final C cex) {
        return new Unsafe<>(cex);
    }

    public abstract boolean isSpurious();

    public abstract boolean isUnsafe();

    public abstract Spurious<P, C> asSpurious();

    public abstract Unsafe<P, C> asUnsafe();

    /** Represents the spurious result with a refined precision. */
    public static final class Spurious<P extends Prec, C extends Cex> extends RefinerResult<P, C> {

        private final P refinedPrec;

        private Spurious(final P refinedPrec) {
            this.refinedPrec = checkNotNull(refinedPrec);
        }

        public P getRefinedPrec() {
            return refinedPrec;
        }

        @Override
        public boolean isSpurious() {
            return true;
        }

        @Override
        public boolean isUnsafe() {
            return false;
        }

        @Override
        public Spurious<P, C> asSpurious() {
            return this;
        }

        @Override
        public Unsafe<P, C> asUnsafe() {
            throw new ClassCastException(
                    "Cannot cast "
                            + Spurious.class.getSimpleName()
                            + " to "
                            + Unsafe.class.getSimpleName());
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(RefinerResult.class.getSimpleName())
                    .add(getClass().getSimpleName())
                    .toString();
        }
    }

    /** Represents the unsafe result with a feasible counterexample. */
    public static final class Unsafe<P extends Prec, C extends Cex> extends RefinerResult<P, C> {

        private final C cex;

        private Unsafe(final C cex) {
            this.cex = checkNotNull(cex);
        }

        public C getCex() {
            return cex;
        }

        @Override
        public boolean isSpurious() {
            return false;
        }

        @Override
        public boolean isUnsafe() {
            return true;
        }

        @Override
        public Spurious<P, C> asSpurious() {
            throw new ClassCastException(
                    "Cannot cast "
                            + Unsafe.class.getSimpleName()
                            + " to "
                            + Spurious.class.getSimpleName());
        }

        @Override
        public Unsafe<P, C> asUnsafe() {
            return this;
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(RefinerResult.class.getSimpleName())
                    .add(getClass().getSimpleName())
                    .toString();
        }
    }
}
