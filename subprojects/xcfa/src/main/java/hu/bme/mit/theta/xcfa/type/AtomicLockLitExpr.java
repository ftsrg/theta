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
package hu.bme.mit.theta.xcfa.type;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.xcfa.XCFA;

import javax.annotation.Nullable;

public class AtomicLockLitExpr extends NullaryExpr<AtomicLockType> implements LitExpr<AtomicLockType> {

	@Nullable
	private final XCFA.Process value;

	public AtomicLockLitExpr(@Nullable XCFA.Process val) {
		value = val;
	}

	@Override
	public AtomicLockType getType() {
		return AtomicLockType.getInstance();
	}

	@Override
	public AtomicLockLitExpr eval(Valuation val) {
		return null;
	}

	@Nullable
	public XCFA.Process getValue() {
		return value;
	}
}
