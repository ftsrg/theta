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
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.TypeUtils;

public final class ArrayWriteExpr<IndexType extends Type, ElemType extends Type>
		implements Expr<ArrayType<IndexType, ElemType>> {

	private static final int HASH_SEED = 1699;

	private static final String OPERATOR_LABEL = "write";

	private volatile int hashCode = 0;

	private final Expr<ArrayType<IndexType, ElemType>> array;
	private final Expr<IndexType> index;
	private final Expr<ElemType> elem;

	private ArrayWriteExpr(final Expr<ArrayType<IndexType, ElemType>> array, final Expr<IndexType> index,
						   final Expr<ElemType> elem) {
		this.array = checkNotNull(array);
		this.index = checkNotNull(index);
		this.elem = checkNotNull(elem);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayWriteExpr<IndexType, ElemType> of(
			final Expr<ArrayType<IndexType, ElemType>> array, final Expr<IndexType> index, final Expr<ElemType> elem) {
		return new ArrayWriteExpr<>(array, index, elem);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayWriteExpr<?, ?> create(final Expr<?> array,
																							  final Expr<?> index, final Expr<?> elem) {
		@SuppressWarnings("unchecked") final ArrayType<IndexType, ElemType> arrayType = (ArrayType<IndexType, ElemType>) array.getType();
		final Expr<ArrayType<IndexType, ElemType>> newArray = cast(array, arrayType);
		final Expr<IndexType> newIndex = cast(index, arrayType.getIndexType());
		final Expr<ElemType> newElem = cast(elem, arrayType.getElemType());
		return ArrayWriteExpr.of(newArray, newIndex, newElem);
	}

	public Expr<ArrayType<IndexType, ElemType>> getArray() {
		return array;
	}

	public Expr<IndexType> getIndex() {
		return index;
	}

	public Expr<ElemType> getElem() {
		return elem;
	}

	@Override
	public ArrayType<IndexType, ElemType> getType() {
		return Array(index.getType(), elem.getType());
	}

	@Override
	public LitExpr<ArrayType<IndexType, ElemType>> eval(final Valuation val) {
		ArrayLitExpr<IndexType, ElemType> arrayVal = (ArrayLitExpr<IndexType, ElemType>)array.eval(val);
		LitExpr<IndexType> indexVal = index.eval(val);
		LitExpr<ElemType> elemVal = elem.eval(val);

		List<Tuple2<Expr<IndexType>, Expr<ElemType>>> elemList = new ArrayList<>();
		for(Tuple2<Expr<IndexType>, Expr<ElemType>> elem : arrayVal.getElements()) {
			if(!elem.get1().equals(indexVal)) {
				elemList.add(elem);
			}
		}
		elemList.add(Tuple2.of(indexVal, elemVal));

		return Array(elemList, arrayVal.getElseElem(), arrayVal.getType());
	}

	@Override
	public int getArity() {
		return 3;
	}

	@Override
	public List<? extends Expr<?>> getOps() {
		return ImmutableList.of(array, index, elem);
	}

	@Override
	public Expr<ArrayType<IndexType, ElemType>> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.size() == 3);
		final Expr<ArrayType<IndexType, ElemType>> newArray = TypeUtils.cast(ops.get(0), array.getType());
		final Expr<IndexType> newIndex = TypeUtils.cast(ops.get(1), index.getType());
		final Expr<ElemType> newElem = TypeUtils.cast(ops.get(2), elem.getType());
		return with(newArray, newIndex, newElem);
	}

	public ArrayWriteExpr<IndexType, ElemType> with(final Expr<ArrayType<IndexType, ElemType>> array,
													final Expr<IndexType> index, final Expr<ElemType> elem) {
		if (this.array == array && this.index == index && elem == this.elem) {
			return this;
		} else {
			return ArrayWriteExpr.of(array, index, elem);
		}
	}

	public ArrayWriteExpr<IndexType, ElemType> withIndex(final Expr<IndexType> index) {
		return with(getArray(), index, getElem());
	}

	public ArrayWriteExpr<IndexType, ElemType> withElem(final Expr<ElemType> elem) {
		return with(getArray(), getIndex(), elem);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + array.hashCode();
			result = 31 * result + index.hashCode();
			result = 31 * result + elem.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ArrayWriteExpr<?, ?>) {
			final ArrayWriteExpr<?, ?> that = (ArrayWriteExpr<?, ?>) obj;
			return this.getArray().equals(that.getArray()) && this.getIndex().equals(that.getIndex())
					&& this.getElem().equals(that.getElem());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(OPERATOR_LABEL).add(array).add(index).add(elem).toString();
	}

}
