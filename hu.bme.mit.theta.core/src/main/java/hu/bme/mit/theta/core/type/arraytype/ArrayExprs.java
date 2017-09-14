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

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class ArrayExprs {

	private ArrayExprs() {
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayType<IndexType, ElemType> Array(
			final IndexType indexType, final ElemType elemType) {
		return new ArrayType<>(indexType, elemType);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayReadExpr<IndexType, ElemType> Read(
			final Expr<ArrayType<IndexType, ElemType>> array, final Expr<IndexType> index) {
		return new ArrayReadExpr<>(array, index);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayWriteExpr<IndexType, ElemType> Write(
			final Expr<ArrayType<IndexType, ElemType>> array, final Expr<IndexType> index, final Expr<ElemType> elem) {
		return new ArrayWriteExpr<>(array, index, elem);
	}

}
