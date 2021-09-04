/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.frontend;

import hu.bme.mit.theta.common.Tuple2;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;

// TODO object clashes when hashcode is the same
public class FrontendMetadata {
	private static final Map<Tuple2<String, ?>, Set<Object>> lookupOwner = new LinkedHashMap<>();
	private static final Map<Tuple2<Object, Integer>, Map<String, Object>> lookupKeyValue = new LinkedHashMap<>();


	public static <T> Set<Object> lookupMetadata(String key, T value) {
		return lookupOwner.getOrDefault(Tuple2.of(key,value), Set.of());
	}
	public static <X> Map<String, ?> lookupMetadata(X owner) {
		return lookupKeyValue.getOrDefault(Tuple2.of(owner, getHashCode(owner)), Map.of());
	}
	public static <X> Optional<Object> getMetadataValue(X owner, String key) {
		return Optional.ofNullable(lookupKeyValue.getOrDefault(Tuple2.of(owner, getHashCode(owner)), Map.of()).get(key));
	}

	public static <T,X> void create(X owner, String key, T value) {
		//checkState(!lookupKeyValue.containsKey(owner) || !lookupKeyValue.get(owner).containsKey(key));
		checkNotNull(value);
		Tuple2<String, T> tup = Tuple2.of(key, value);
		Set<Object> set = lookupOwner.getOrDefault(tup, new LinkedHashSet<>());
		set.add(owner);
		lookupOwner.put(tup, set);
		Map<String, Object> keyvalues = lookupKeyValue.getOrDefault(Tuple2.of(owner, getHashCode(owner)), new LinkedHashMap<>());
		keyvalues.put(key, value);
		lookupKeyValue.put(Tuple2.of(owner, getHashCode(owner)), keyvalues);
	}

	private static int getHashCode(Object object) {
		if(object instanceof String) return object.hashCode();
		else return System.identityHashCode(object);
	}

	public static void clear() {
		lookupKeyValue.clear();
		lookupOwner.clear();
	}
}
