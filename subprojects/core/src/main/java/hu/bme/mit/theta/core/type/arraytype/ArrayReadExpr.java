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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;

public final class ArrayReadExpr<IndexType extends Type, ElemType extends Type> implements Expr<ElemType> {

	private static final int HASH_SEED = 1321;

	private static final String OPERATOR_LABEL = "read";

	private volatile int hashCode = 0;

	private final Expr<ArrayType<IndexType, ElemType>> array;
	private final Expr<IndexType> index;

	private ArrayReadExpr(final Expr<ArrayType<IndexType, ElemType>> array, final Expr<IndexType> index) {
		this.array = checkNotNull(array);
		this.index = checkNotNull(index);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayReadExpr<IndexType, ElemType> of(
			final Expr<ArrayType<IndexType, ElemType>> array, final Expr<IndexType> index) {
		return new ArrayReadExpr<>(array, index);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayReadExpr<?, ?> create(final Expr<?> array,
																							 final Expr<?> index) {
		@SuppressWarnings("unchecked") final ArrayType<IndexType, ElemType> arrayType = (ArrayType<IndexType, ElemType>) array.getType();
		final Expr<ArrayType<IndexType, ElemType>> newArray = cast(array, arrayType);
		final Expr<IndexType> newIndex = cast(index, arrayType.getIndexType());
		return ArrayReadExpr.of(newArray, newIndex);
	}

	public Expr<ArrayType<IndexType, ElemType>> getArray() {
		return array;
	}

	public Expr<IndexType> getIndex() {
		return index;
	}

	@Override
	public ElemType getType() {
		return array.getType().getElemType();
	}

	@Override
	public LitExpr<ElemType> eval(final Valuation val) {
		ArrayLitExpr<IndexType, ElemType> arrayVal = (ArrayLitExpr<IndexType, ElemType>)array.eval(val);
		LitExpr<IndexType> indexVal = index.eval(val);
		for (Tuple2<Expr<IndexType>, Expr<ElemType>> elem : arrayVal.getElements()) {
			if (elem.get1().equals(indexVal)){
				return (LitExpr<ElemType>)elem.get2();
			}
		}
		return (LitExpr<ElemType>)arrayVal.getElseElem();
	}

	@Override
	public int getArity() {
		return 2;
	}

	@Override
	public List<Expr<?>> getOps() {
		return ImmutableList.of(array, index);
	}

	@Override
	public Expr<ElemType> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.size() == 2);
		final Expr<ArrayType<IndexType, ElemType>> newArray = cast(ops.get(0), array.getType());
		final Expr<IndexType> newIndex = cast(ops.get(1), index.getType());
		return with(newArray, newIndex);
	}

	public ArrayReadExpr<IndexType, ElemType> with(final Expr<ArrayType<IndexType, ElemType>> array,
												   final Expr<IndexType> index) {
		if (this.array == array && this.index == index) {
			return this;
		} else {
			return ArrayReadExpr.of(array, index);
		}
	}

	public ArrayReadExpr<IndexType, ElemType> withArray(final Expr<ArrayType<IndexType, ElemType>> array) {
		return with(array, getIndex());
	}

	public ArrayReadExpr<IndexType, ElemType> withIndex(final Expr<IndexType> index) {
		return with(getArray(), index);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + array.hashCode();
			result = 31 * result + index.hashCode();
			hashCode = result;
		}

		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ArrayReadExpr<?, ?>) {
			final ArrayReadExpr<?, ?> that = (ArrayReadExpr<?, ?>) obj;
			return this.getArray().equals(that.getArray()) && this.getIndex().equals(that.getIndex());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(OPERATOR_LABEL).add(array).add(index).toString();
	}

}
