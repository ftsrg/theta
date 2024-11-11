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
package hu.bme.mit.theta.common.logging;

/** Interface for logging within algorithms. */
public interface Logger {

    /** Detailedness of logging in order. */
    public enum Level {
        RESULT,
        MAINSTEP,
        SUBSTEP,
        INFO,
        DETAIL,
        VERBOSE
    }

    /**
     * Write objects with a given level and pattern
     *
     * @param level Level
     * @param pattern Pattern for {@link String#format(String, Object...)}
     * @param objects Objects to be substituted in the pattern
     * @return Logger instance
     */
    Logger write(Level level, String pattern, Object... objects);

    default Logger writeln(Level level, String pattern, Object... objects) {
        return write(level, pattern + "%n", objects);
    }
}
