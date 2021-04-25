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

package hu.bme.mit.theta.xcfa.model;

import hu.bme.mit.theta.common.Tuple2;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class XcfaMetadata<T,X> {
	private static final Map<Tuple2<String, ?>, Set<Object>> lookupOwner = new HashMap<>();
	private static final Map<Object, Map<String, Object>> lookupKeyValue = new HashMap<>();


	public static <T> Set<Object> lookupMetadata(String key, T value) {
		return lookupOwner.get(Tuple2.of(key,value));
	}
	public static <X> Map<String, ?> lookupMetadata(X owner) {
		return lookupKeyValue.get(owner);
	}
	public static <X> Object getMetadataValue(X owner, String key) {
		return lookupKeyValue.get(owner).get(key);
	}

	public static <T,X> void create(X owner, String key, T value) {
		Tuple2<String, T> tup = Tuple2.of(key, value);
		Set<Object> set = lookupOwner.getOrDefault(tup, new HashSet<>());
		set.add(owner);
		lookupOwner.put(tup, set);
		Map<String, Object> keyvalues = lookupKeyValue.getOrDefault(owner, new HashMap<>());
		keyvalues.put(key, value);
		lookupKeyValue.put(owner, keyvalues);
	}
}
