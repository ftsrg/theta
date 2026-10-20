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
package hu.bme.mit.theta.frontend;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.jetbrains.annotations.NotNull;

public class FrontendMetadata {
    private final Map<Integer, Map<String, Object>> lookupKeyValue;

    // Keys of String owners: unlike identity hashes, these mean the same in another process.
    private final Set<Integer> stringKeys;

    public FrontendMetadata() {
        this.lookupKeyValue = new LinkedHashMap<>();
        this.stringKeys = new LinkedHashSet<>();
    }

    public FrontendMetadata(@NotNull Map<Integer, Map<String, Object>> lookupKeyValue) {
        this.lookupKeyValue = new LinkedHashMap<>(lookupKeyValue);
        this.stringKeys = new LinkedHashSet<>();
    }

    public <X> Optional<Object> getMetadataValue(X owner, String key) {
        return Optional.ofNullable(
                lookupKeyValue.getOrDefault(getHashCode(owner), Map.of()).get(key));
    }

    public <T, X> void create(X owner, String key, T value) {
        checkNotNull(value);
        Map<String, Object> keyvalues =
                lookupKeyValue.getOrDefault(getHashCode(owner), new LinkedHashMap<>());
        keyvalues.put(key, value);
        lookupKeyValue.put(getHashCode(owner), keyvalues);
        if (owner instanceof String) {
            stringKeys.add(getHashCode(owner));
        }
    }

    public Map<Integer, Map<String, Object>> getLookupKeyValue() {
        return new LinkedHashMap<>(lookupKeyValue);
    }

    /** The keys of {@link #getLookupKeyValue()} that belong to String owners. */
    public Set<Integer> getStringKeys() {
        return new LinkedHashSet<>(stringKeys);
    }

    /**
     * Adds {@code values} under {@code key}, as {@link #create} does for an owner with that key.
     * Deserialization uses it, having re-keyed the owners to the decoded objects.
     */
    public void restore(int key, boolean stringOwner, Map<String, Object> values) {
        lookupKeyValue.computeIfAbsent(key, k -> new LinkedHashMap<>()).putAll(values);
        if (stringOwner) {
            stringKeys.add(key);
        }
    }

    private static int getHashCode(Object object) {
        if (object instanceof String) {
            return object.hashCode();
        } else {
            return System.identityHashCode(object);
        }
    }
}
