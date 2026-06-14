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
package hu.bme.mit.theta.frontend.petrinet.model;

import java.io.File;
import org.jetbrains.annotations.Nullable;

public enum PropType {
    TARGET_MARKING,
    DEADLOCK,
    PN_SAFE,
    FULL_EXPLORATION;

    /**
     * Returns a petrinet property type from a filename. E.g., pn_safe.prp -> PN_SAFE Does not parse
     * the contents.
     *
     * @param property the property file to use
     * @return the petrinet property value
     */
    public static PropType fromFilename(@Nullable File property) {
        if (property == null) return PropType.FULL_EXPLORATION;
        return PropType.valueOf(property.getName().split("\\.")[0].toUpperCase());
    }
}
