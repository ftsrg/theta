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
package hu.bme.mit.theta.common;

public final class Unit {

	private static final int HASH_CODE = 1261289;
	private static final String TO_STRING = "()";

	private static final Unit UNIT = new Unit();

	private Unit() {
	}

	public static Unit unit() {
		return UNIT;
	}

	@Override
	public int hashCode() {
		return HASH_CODE;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof Unit;
	}

	@Override
	public String toString() {
		return TO_STRING;
	}

}
