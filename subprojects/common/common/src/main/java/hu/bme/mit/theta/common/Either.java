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
package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.NoSuchElementException;

public abstract class Either<L, R> {

    private Either() {}

    public static <L> Left<L, ?> Left(final L left) {
        return new Left<>(left);
    }

    public static <R> Right<?, R> Right(final R right) {
        return new Right<>(right);
    }

    public abstract boolean isLeft();

    public abstract boolean isRight();

    public abstract L left();

    public abstract R right();

    ////

    public static final class Left<L, R> extends Either<L, R> {

        private static final int HASH_SEED = 6427;
        private volatile int hashCode = 0;

        private final L left;

        private Left(final L left) {
            this.left = checkNotNull(left);
        }

        @Override
        public boolean isLeft() {
            return true;
        }

        @Override
        public boolean isRight() {
            return false;
        }

        @Override
        public L left() {
            return left;
        }

        @Override
        public R right() {
            throw new NoSuchElementException();
        }

        @Override
        public int hashCode() {
            int result = hashCode;
            if (result == 0) {
                result = HASH_SEED;
                result = 31 * result + left.hashCode();
                hashCode = result;
            }
            return result;
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            } else if (obj != null && this.getClass() == obj.getClass()) {
                final Left<?, ?> that = (Left<?, ?>) obj;
                return this.left.equals(that.left);
            } else {
                return false;
            }
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder("left").add(left).toString();
        }
    }

    public static final class Right<L, R> extends Either<L, R> {

        private static final int HASH_SEED = 4801;
        private volatile int hashCode = 0;

        private final R right;

        private Right(final R right) {
            this.right = checkNotNull(right);
        }

        @Override
        public boolean isLeft() {
            return false;
        }

        @Override
        public boolean isRight() {
            return true;
        }

        @Override
        public L left() {
            throw new NoSuchElementException();
        }

        @Override
        public R right() {
            return right;
        }

        @Override
        public int hashCode() {
            int result = hashCode;
            if (result == 0) {
                result = HASH_SEED;
                result = 31 * result + right.hashCode();
                hashCode = result;
            }
            return result;
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            } else if (obj != null && this.getClass() == obj.getClass()) {
                final Right<?, ?> that = (Right<?, ?>) obj;
                return this.right.equals(that.right);
            } else {
                return false;
            }
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder("right").add(right).toString();
        }
    }
}
