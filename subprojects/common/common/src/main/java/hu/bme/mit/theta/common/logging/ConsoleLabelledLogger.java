/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import java.io.PrintStream;

public final class ConsoleLabelledLogger implements Logger {

    private static final PrintStream CONSOLE = System.out;

    @Override
    public Logger write(Level level, String pattern, Object... objects) {
        CONSOLE.printf(level + "\t{" + pattern.replace("}", "]") + "}", objects);
        return this;
    }
}
