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
package hu.bme.mit.theta.core.type.pointertype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;

public final class NullExpr<PointedType extends Type> extends NullaryExpr<PointerType<PointedType>>
		implements LitExpr<PointerType<PointedType>> {

	private static final NullExpr<?> INSTANCE = new NullExpr<>();
	private static final String EXPR_LABEL = "Null";
	private static final int HASH_SEED = 1632143;

	private NullExpr() {
	}

	@SuppressWarnings("unchecked")
	static <PointedType extends Type> NullExpr<PointedType> getInstance() {
		return (NullExpr<PointedType>) INSTANCE;
	}

	@Override
	public PointerType<PointedType> getType() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public LitExpr<PointerType<PointedType>> eval(final Valuation val) {
		return this;
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof NullExpr);
	}

	@Override
	public String toString() {
		return EXPR_LABEL;
	}

}
