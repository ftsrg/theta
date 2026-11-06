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
package hu.bme.mit.theta.common.logging;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

public class BaseLoggerTest {

    private static final class StringLogger extends BaseLogger {
        private final StringBuilder out = new StringBuilder();

        StringLogger() {
            super(Level.VERBOSE);
        }

        @Override
        protected void writeStr(String str) {
            out.append(str);
        }
    }

    @Test
    public void formatsArguments() {
        StringLogger logger = new StringLogger();
        logger.write(Logger.Level.INFO, "%s=%d", "x", 1);
        assertEquals("x=1", logger.out.toString());
    }

    @Test
    public void writesTextWithAStrayPercentAsIs() {
        StringLogger logger = new StringLogger();
        logger.info("Could not emit witness: printf(\"%.2f\", x)");
        assertEquals(
                "Could not emit witness: printf(\"%.2f\", x)" + System.lineSeparator(),
                logger.out.toString());
    }
}
