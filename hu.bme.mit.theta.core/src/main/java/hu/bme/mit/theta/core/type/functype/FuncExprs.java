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
package hu.bme.mit.theta.core.type.functype;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class FuncExprs {

	private FuncExprs() {
	}

	public static <ParamType extends Type, ResultType extends Type> FuncType<ParamType, ResultType> Func(
			final ParamType paramType, final ResultType resultType) {
		return new FuncType<>(paramType, resultType);
	}

	public static <ParamType extends Type, ResultType extends Type> FuncLitExpr<ParamType, ResultType> Func(
			final ParamDecl<ParamType> paramDecl, final Expr<ResultType> result) {
		return new FuncLitExpr<>(paramDecl, result);
	}

	public static <ParamType extends Type, ResultType extends Type> FuncAppExpr<ParamType, ResultType> App(
			final Expr<FuncType<ParamType, ResultType>> func, final Expr<ParamType> param) {
		return new FuncAppExpr<>(func, param);
	}

}
