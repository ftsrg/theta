/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.alt.expl;

public abstract class Safety {
    public abstract boolean isSafe();
    public abstract boolean isFinished();

    @Override
    public String toString() {
        return "Unknown";
    }

    final static class Safe extends Safety {

        final static class LazyHolder {
            final static Safe instance = new Safe();
        }

        static Safe getInstance() {
            return LazyHolder.instance;
        }

        @Override
        public boolean isSafe() {
            return true;
        }

        @Override
        public boolean isFinished() {
            return false;
        }

        @Override
        public String toString() {
            return "Safe";
        }
    }

    static class Unsafe extends Safety {

        private final String message;

        public Unsafe(String message) {
            this.message = message;
        }

        @Override
        public boolean isSafe() {
            return false;
        }

        @Override
        public boolean isFinished() {
            return true;
        }

        @Override
        public String toString() {
            return "Unsafe: " + message;
        }
    }

    final static class Finished extends Safety {

        final static class LazyHolder {
            final static Finished instance = new Finished();
        }

        static Finished getInstance() {
            return LazyHolder.instance;
        }

        @Override
        public boolean isSafe() {
            return true;
        }

        @Override
        public boolean isFinished() {
            return true;
        }
    }

    static Safety safe() {
        return Safe.getInstance();
    }

    static Finished finished() {
        return Finished.getInstance();
    }

    static Unsafe unsafe(String message) {
        return new Unsafe(message);
    }
}
