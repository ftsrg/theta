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
package hu.bme.mit.theta.analysis.waitlist;

import java.util.Collection;
import java.util.stream.Stream;

/**
 * Generic interface for waitlists. Elements added to a waitlist are removed in
 * a specific order that the implementations determine.
 */
public interface Waitlist<T> {
	void add(T item);

	void addAll(Collection<? extends T> items);

	void addAll(Stream<? extends T> items);

	boolean isEmpty();

	T remove();

	int size();

	void clear();
}
