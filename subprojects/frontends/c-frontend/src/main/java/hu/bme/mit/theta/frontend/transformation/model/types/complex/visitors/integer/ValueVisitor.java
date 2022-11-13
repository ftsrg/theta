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

package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer;

import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;

import java.math.BigInteger;
import java.util.List;

import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class ValueVisitor extends CComplexType.CComplexTypeVisitor<String, LitExpr<?>> {
	public static final ValueVisitor instance = new ValueVisitor();

	@Override
	public LitExpr<?> visit(CInteger type, String param) {
		return Int(new BigInteger(param));
	}

	@Override
	public LitExpr<?> visit(CArray type, String param) {
		return getExpr(type, param);
	}

	private <IndexType extends Type, ElemType extends Type> ArrayLitExpr<IndexType, ElemType> getExpr(CArray type, String param) {
		//noinspection unchecked
		ArrayType<IndexType, ElemType> smtType = (ArrayType<IndexType, ElemType>) type.getSmtType();
		return Array(List.of(), cast(type.getEmbeddedType().getValue(param), smtType.getElemType()), smtType);
	}
}
