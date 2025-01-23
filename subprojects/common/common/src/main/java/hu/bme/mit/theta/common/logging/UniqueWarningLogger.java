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

import java.util.LinkedHashSet;
import java.util.Set;

public final class UniqueWarningLogger implements Logger {
    private final Set<String> messages;
    private final Logger logger;

    public UniqueWarningLogger(Logger logger) {
        this.logger = logger;
        messages = new LinkedHashSet<>();
    }

    @Override
    public Logger write(Level level, String pattern, Object... objects) {
        if (!messages.contains(pattern)) {
            messages.add(pattern);
            logger.write(level, pattern, objects);
        }
        return this;
    }
}
