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
package hu.bme.mit.theta.frontend;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;
import org.jetbrains.annotations.NotNull;

public class FrontendMetadata {
    private final Map<Integer, Map<String, Object>> lookupKeyValue;
    private final Map<Tuple2<Expr<?>, Integer>, CComplexType> types;

    public FrontendMetadata() {
        this.lookupKeyValue = new LinkedHashMap<>();
        this.types = new LinkedHashMap<>();
    }

    public FrontendMetadata(@NotNull Map<Integer, Map<String, Object>> lookupKeyValue) {
        this.lookupKeyValue = new LinkedHashMap<>(lookupKeyValue);
        this.types = new LinkedHashMap<>();
    }

    public <X> Map<String, ?> lookupMetadata(X owner) {
        return lookupKeyValue.getOrDefault(getHashCode(owner), Map.of());
    }

    public <X> Optional<Object> getMetadataValue(X owner, String key) {
        if (owner instanceof Expr<?> && key.equals("cType")) {
            Tuple2<Expr<?>, Integer> pair =
                    Tuple2.of((Expr<?>) owner, System.identityHashCode(owner));
            return Optional.ofNullable(types.get(pair));
        }
        return Optional.ofNullable(
                lookupKeyValue.getOrDefault(getHashCode(owner), Map.of()).get(key));
    }

    public <T, X> void create(X owner, String key, T value) {
        checkNotNull(value);
        if (owner instanceof Expr<?> && key.equals("cType") && value instanceof CComplexType) {
            Tuple2<Expr<?>, Integer> pair =
                    Tuple2.of((Expr<?>) owner, System.identityHashCode(owner));
            //            if (types.containsKey(pair) && types.get(pair).getClass() !=
            // value.getClass()) {
            //                throw new RuntimeException("Expression (" + owner + ") already has a
            // different type: " + types.get(pair) + ". New type: " + value);
            //            }
            types.put(pair, (CComplexType) value);
        } else {
            Map<String, Object> keyvalues =
                    lookupKeyValue.getOrDefault(getHashCode(owner), new LinkedHashMap<>());
            keyvalues.put(key, value);
            lookupKeyValue.put(getHashCode(owner), keyvalues);
        }
    }

    public Map<Integer, Map<String, Object>> getLookupKeyValue() {
        return new LinkedHashMap<>(lookupKeyValue);
    }

    public Map<Tuple2<Expr<?>, Integer>, CComplexType> getTypes() {
        return new LinkedHashMap<>(types);
    }

    private static int getHashCode(Object object) {
        if (object instanceof String) {
            return object.hashCode();
        } else {
            return System.identityHashCode(object);
        }
    }
}
