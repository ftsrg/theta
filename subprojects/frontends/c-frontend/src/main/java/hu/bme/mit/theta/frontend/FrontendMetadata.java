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

package hu.bme.mit.theta.frontend;

import org.jetbrains.annotations.NotNull;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkNotNull;

public class FrontendMetadata {
    private final Map<Integer, Map<String, Object>> lookupKeyValue;

    public FrontendMetadata() {
        this.lookupKeyValue = new LinkedHashMap<>();
    }

    public FrontendMetadata(@NotNull Map<Integer, Map<String, Object>> lookupKeyValue) {
        this.lookupKeyValue = new LinkedHashMap<>(lookupKeyValue);
    }

    public <X> Map<String, ?> lookupMetadata(X owner) {
        return lookupKeyValue.getOrDefault(getHashCode(owner), Map.of());
    }

    public <X> Optional<Object> getMetadataValue(X owner, String key) {
        return Optional.ofNullable(lookupKeyValue.getOrDefault(getHashCode(owner), Map.of()).get(key));
    }

    public <T, X> void create(X owner, String key, T value) {
        checkNotNull(value);
        Map<String, Object> keyvalues = lookupKeyValue.getOrDefault(getHashCode(owner), new LinkedHashMap<>());
        keyvalues.put(key, value);
        lookupKeyValue.put(getHashCode(owner), keyvalues);
    }

    public Map<Integer, Map<String, Object>> getLookupKeyValue() {
        return new LinkedHashMap<>(lookupKeyValue);
    }

    private static int getHashCode(Object object) {
        if (object instanceof String) {
            return object.hashCode();
        } else {
            return System.identityHashCode(object);
        }
    }
}
