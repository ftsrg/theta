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
package hu.bme.mit.theta.common.product;

import com.google.common.collect.ImmutableList;

public final class Tuple1<T1> extends Tuple implements Product1<T1> {

	Tuple1(final T1 e1) {
		super(ImmutableList.of(e1));
	}

	@Override
	public T1 _1() {
		@SuppressWarnings("unchecked")
		final T1 result = (T1) elem(0);
		return result;
	}

}
