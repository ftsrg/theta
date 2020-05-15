/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.alt.algorithm;

import com.google.common.base.Preconditions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Helps return the list of good tests.
 */
public class FileListHelper {

    public interface Config {
        boolean atomicSupported();
        boolean mutexSupported();
        boolean functionSupported();
        boolean stateGraphLoopSupported();
        boolean multiThreadSupported();
        boolean safeSupported();
        boolean unsafeSupported();
        boolean bigSupported();
    }

    private static final class ConfigImpl implements Config {

        private final boolean atomic;
        private final boolean mutex;
        private final boolean function;
        private final boolean loop;
        private final boolean threads;
        private final boolean safe;
        private final boolean unsafe;
        private final boolean big;

        /**
         * Usage: Atomic, Mutex, function, loop
         * "All" can be used for all support
         */
        private ConfigImpl(String configString) {
            configString = configString.toLowerCase();
            if ("all".equals(configString)) {
                atomic = mutex = function = loop = threads = safe = unsafe = big = true;
            } else {
                atomic = configString.contains("atomic");
                mutex = configString.contains("mutex");
                function = configString.contains("function");
                loop = configString.contains("loop");
                threads = configString.contains("threads");
                safe = configString.contains("safe");
                unsafe = configString.contains("unsafe");
                big = configString.contains("big");
            }
            Preconditions.checkArgument(safe || unsafe, "At least one of safe or unsafe should be added!");
        }

        @Override
        public boolean atomicSupported() {
            return atomic;
        }

        @Override
        public boolean mutexSupported() {
            return mutex;
        }

        @Override
        public boolean functionSupported() {
            return function;
        }

        @Override
        public boolean stateGraphLoopSupported() {
            return loop;
        }

        @Override
        public boolean multiThreadSupported() {
            return threads;
        }

        @Override
        public boolean safeSupported() {
            return safe;
        }

        @Override
        public boolean unsafeSupported() {
            return unsafe;
        }

        @Override
        public boolean bigSupported() {
            return big;
        }
    }

    public static List<Object[]> tests(String c) {
        return tests(new ConfigImpl(c));
    }

    public static ArrayList<Object[]> filterSafe(ArrayList<Object[]> original, Config c) {
        if (!c.safeSupported()) {
            return original.stream().filter(t ->
                    !((Boolean) t[1]) // remove safe
            ).collect(Collectors.toCollection(ArrayList::new));
        }
        return original;
    }

    public static ArrayList<Object[]> filterUnsafe(ArrayList<Object[]> original, Config c) {
        if (!c.unsafeSupported()) {
            return original.stream().filter(t ->
                    (Boolean) t[1] // remove unsafe
            ).collect(Collectors.toCollection(ArrayList::new));
        }
        return original;
    }

    public static void functions(ArrayList<Object[]> result, Config c) {
        if (c.functionSupported()) {
            if (c.multiThreadSupported()) {
                result.add(
                        new Object[]{"/functions-global-local.xcfa", true}
                );
            }
            result.addAll(Arrays.asList(
                    new Object[]{"/fibonacci.xcfa", true},
                    new Object[]{"/gcd.xcfa", true}
            ));
        }
    }

    public static void atomics(ArrayList<Object[]> result, Config c) {
        if (c.multiThreadSupported() && c.atomicSupported()) {
            result.add(
                    new Object[]{"/atomic.xcfa", true}
            );
        }
    }

    public static void mutexes(ArrayList<Object[]> result, Config c) {
        if (c.mutexSupported()) {
            if (c.multiThreadSupported()) {
                result.addAll(Arrays.asList(
                        new Object[]{"/mutex-test3.xcfa", false},
                        new Object[]{"/mutex-test4.xcfa", true},
                        new Object[]{"/waitnotify.xcfa", false}
                ));
            }
            result.addAll(Arrays.asList(
                    new Object[]{"/mutex-test.xcfa", true},
                    new Object[]{"/mutex-test2.xcfa", false}
            ));
        }
    }

    public static List<Object[]> tests(Config c) {
        ArrayList<Object[]> result = new ArrayList<>();
        functions(result, c);
        atomics(result, c);
        mutexes(result, c);
        if (c.stateGraphLoopSupported()) {
            result.add(
                    new Object[]{"/infiniteloop.xcfa", true}
            );
        }
        if (c.multiThreadSupported()) {
            result.addAll(Arrays.asList(
                    new Object[]{"/partialorder-test.xcfa", false},
                    new Object[]{"/partialorder-test2.xcfa", false},
                    new Object[]{"/partialorder-test3.xcfa", false},
                    new Object[]{"/partialorder-test4.xcfa", false},
                    new Object[]{"/partialorder-min-test.xcfa", false}
                    ));
            if (c.stateGraphLoopSupported()) {
                result.add(new Object[]{"/partialorder-test2.xcfa", false});
            }
            if (c.bigSupported()) {
                result.add(new Object[]{"/very-parallel.xcfa", true});

            }
        }
        result.addAll(Arrays.asList(
                new Object[]{"/simple-test.xcfa", true},
                new Object[]{"/deadlock.xcfa", false}
                ));

        result = filterSafe(result, c);
        result = filterUnsafe(result, c);

        return result;
    }
}
