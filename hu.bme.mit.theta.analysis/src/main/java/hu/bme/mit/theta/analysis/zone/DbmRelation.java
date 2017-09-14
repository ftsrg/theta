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
package hu.bme.mit.theta.analysis.zone;

enum DbmRelation {
	LESS(true, false), GREATER(false, true), EQUAL(true, true), INCOMPARABLE(false, false);

	private final boolean leq;
	private final boolean geq;

	private DbmRelation(final boolean leq, final boolean geq) {
		this.leq = leq;
		this.geq = geq;
	}

	public static DbmRelation create(final boolean leq, final boolean geq) {
		if (leq) {
			if (geq) {
				return DbmRelation.EQUAL;
			} else {
				return DbmRelation.LESS;
			}
		} else {
			if (geq) {
				return DbmRelation.GREATER;
			} else {
				return DbmRelation.INCOMPARABLE;
			}
		}
	}

	public boolean isLeq() {
		return leq;
	}

	public boolean isGeq() {
		return geq;
	}
}
