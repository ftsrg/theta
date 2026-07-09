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
package hu.bme.mit.theta.common.logging;

import java.util.UnknownFormatConversionException;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * Logger.write treats its String argument as a String.format pattern. Dynamic content (config
 * dumps, exception messages, file paths) may contain '%'. Call sites must pass such content as a
 * format argument (e.g. "%s"), not as the pattern itself. These tests document that contract; the
 * SV-COMP run crashed 60+ times with UnknownFormatConversionException from call sites that violated
 * it.
 */
public class LoggerFormatSafetyTest {

    private static final class CapturingLogger extends BaseLogger {
        final StringBuilder sb = new StringBuilder();

        CapturingLogger() {
            super(Logger.Level.RESULT);
        }

        @Override
        protected void writeStr(String str) {
            sb.append(str);
        }
    }

    @Test
    public void dynamicContentPassedAsArgumentIsSafe() {
        CapturingLogger logger = new CapturingLogger();
        String dynamic = "Analysis result: 100% (a.b) done";
        logger.write(Logger.Level.RESULT, "%s", dynamic);
        Assertions.assertEquals(dynamic, logger.sb.toString());
    }

    @Test
    public void resultHelperWithDynamicArgumentIsSafe() {
        CapturingLogger logger = new CapturingLogger();
        // mirrors the fixed `logger.result("%s", status.toString())` call-site pattern
        logger.result("%s", "status with a stray % and a .conversion");
        Assertions.assertTrue(logger.sb.toString().startsWith("status with a stray %"));
    }

    @Test
    public void dynamicContentAsPatternThrows() {
        CapturingLogger logger = new CapturingLogger();
        // the pre-fix anti-pattern: interpolated content used as the format pattern
        Assertions.assertThrows(
                UnknownFormatConversionException.class,
                () -> logger.write(Logger.Level.RESULT, "Conversion = '%.' here"));
    }
}
