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

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.pointertype.PointerExprs.Pointer;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;

public final class NewExpr<PointedType extends Type> extends NullaryExpr<PointerType<PointedType>> {

	private static final int HASH_SEED = 8699;
	private volatile int hashCode = 0;

	private static final String EXPR_LABEL = "new";

	private final PointedType pointedType;

	NewExpr(final PointedType pointedType) {
		this.pointedType = checkNotNull(pointedType);
	}

	public PointedType getPointedType() {
		return pointedType;
	}

	@Override
	public PointerType<PointedType> getType() {
		return Pointer(pointedType);
	}

	@Override
	public LitExpr<PointerType<PointedType>> eval(final Valuation val) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + pointedType.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof NewExpr) {
			final NewExpr<?> that = (NewExpr<?>) obj;
			return this.getPointedType().equals(that.getPointedType());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(EXPR_LABEL).add(pointedType).toString();
	}

}
