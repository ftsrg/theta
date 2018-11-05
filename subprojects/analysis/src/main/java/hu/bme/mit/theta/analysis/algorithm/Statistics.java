/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

/**
 * Base class for storing statistics as key-value pairs. Derived classes can add
 * new statistics which can then be queried.
 */
public abstract class Statistics {

	private final Map<String, Supplier<Object>> stats;

	protected Statistics() {
		stats = new LinkedHashMap<>();
	}

	/**
	 * Add a new statistic.
	 */
	protected void addStat(final String key, final Supplier<Object> value) {
		stats.put(key, value);
	}

	/**
	 * Gets the set of keys.
	 */
	public final Set<String> keySet() {
		return Collections.unmodifiableSet(stats.keySet());
	}

	/**
	 * Gets the value for a given key. The key must exist.
	 */
	public final Object get(final String key) {
		checkArgument(stats.containsKey(key), "Key not found");
		return stats.get(key).get();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final String key : keySet()) {
			sb.append(key).append(": ").append(get(key)).append(System.lineSeparator());
		}
		return sb.toString();
	}
}
