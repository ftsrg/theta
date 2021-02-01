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
package hu.bme.mit.theta.core.type.arraytype;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;

public final class ArrayType<IndexType extends Type, ElemType extends Type>
		implements Equational<ArrayType<IndexType, ElemType>> {

	private final static int HASH_SEED = 4919;
	private final static String TYPE_LABEL = "Array";

	private final IndexType indexType;
	private final ElemType elemType;

	private volatile int hashCode = 0;

	private ArrayType(final IndexType indexType, final ElemType elemType) {
		this.indexType = checkNotNull(indexType);
		this.elemType = checkNotNull(elemType);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayType<IndexType, ElemType> of(
			final IndexType indexType, final ElemType elemType) {
		return new ArrayType<>(indexType, elemType);
	}

	public IndexType getIndexType() {
		return indexType;
	}

	public ElemType getElemType() {
		return elemType;
	}

	@Override
	public EqExpr<ArrayType<IndexType, ElemType>> Eq(final Expr<ArrayType<IndexType, ElemType>> leftOp,
													 final Expr<ArrayType<IndexType, ElemType>> rightOp) {
		return ArrayExprs.Eq(leftOp, rightOp);
	}

	@Override
	public NeqExpr<ArrayType<IndexType, ElemType>> Neq(final Expr<ArrayType<IndexType, ElemType>> leftOp,
													   final Expr<ArrayType<IndexType, ElemType>> rightOp) {
		return ArrayExprs.Neq(leftOp, rightOp);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + indexType.hashCode();
			result = 31 * result + elemType.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> that = (ArrayType<?, ?>) obj;
			return this.getIndexType().equals(that.getIndexType()) && this.getElemType().equals(that.getElemType());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final String indexString = String.format("([%s] -> %s)", indexType, elemType);
		return Utils.lispStringBuilder(TYPE_LABEL).add(indexString).toString();
	}
}
