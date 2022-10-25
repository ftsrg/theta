/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.common.datalog;

public class GenericDatalogArgument<T> implements DatalogArgument {
	private final T content;

	private GenericDatalogArgument(T content) {
		this.content = content;
	}

	public static <T> GenericDatalogArgument<T> createArgument(T content) {
		return new GenericDatalogArgument<>(content);
	}

	public T getContent() {
		return content;
	}

	@Override
	public String toString() {
		return content.toString();
	}

	@Override
	public boolean equals(Object o) {
		if (o instanceof GenericDatalogArgument) return content.equals(((GenericDatalogArgument<?>) o).getContent());
		else return content.equals(o);
	}

	@Override
	public int hashCode() {
		return content.hashCode();
	}
}
