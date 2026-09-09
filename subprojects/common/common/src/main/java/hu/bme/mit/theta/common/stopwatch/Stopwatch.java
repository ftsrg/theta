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
package hu.bme.mit.theta.common.stopwatch;

import java.util.concurrent.TimeUnit;

public interface Stopwatch {

    void start();

    void stop();

    void reset();

    boolean isRunning();

    long elapsedNanos();

    long elapsedMillis();

    default long elapsed(TimeUnit desiredUnit) {
        return desiredUnit.convert(this.elapsedNanos(), TimeUnit.NANOSECONDS);
    }

    default Stopwatch measure(Runnable runnable) {
        this.start();
        runnable.run();
        this.stop();
        return this;
    }

    static Stopwatch create() {
        return CgroupStopwatch.Companion.detectCgroupVersion() > 0
                ? new CgroupStopwatch()
                : new GuavaStopwatch(); // TODO: log that time measurements may be imprecise
    }

    static Stopwatch createStarted() {
        Stopwatch stopwatch = create();
        stopwatch.start();
        return stopwatch;
    }

    static Stopwatch createUnstarted() {
        return create();
    }
}
