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

package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer;

import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class Fitsall extends CInteger implements Unsigned {
	private static final int RANK = 100;

	public Fitsall(CSimpleType origin) {
		super(origin);
		rank = RANK;
		unsigned = false;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}


	@Override
	public String getTypeName() {
		return "fitsall";
	}

	@Override
	public CInteger getSignedVersion() {
		throw new RuntimeException("Bool does not have a signed version!");
	}

	@Override
	public CInteger getUnsignedVersion() {
		return this;
	}
}
