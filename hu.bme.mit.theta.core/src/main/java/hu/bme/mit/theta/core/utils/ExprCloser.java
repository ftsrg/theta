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
package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.Decls.Param;
import static java.lang.String.format;

import java.util.Map;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

final class ExprCloser {

	private static final String PARAM_NAME_FORMAT = "_%s_p";

	private ExprCloser() {
	}

	static <T extends Type> Expr<T> close(final Expr<T> expr, final Map<VarDecl<?>, ParamDecl<?>> mapping) {
		if (expr instanceof RefExpr) {
			final RefExpr<T> ref = (RefExpr<T>) expr;
			final Decl<T> decl = ref.getDecl();
			if (decl instanceof VarDecl) {
				final VarDecl<T> varDecl = (VarDecl<T>) decl;
				final ParamDecl<?> param = mapping.computeIfAbsent(varDecl,
						v -> Param(format(PARAM_NAME_FORMAT, v.getName()), v.getType()));
				final Expr<T> paramRef = TypeUtils.cast(param.getRef(), expr.getType());
				return paramRef;
			}
		}

		return expr.map(op -> close(op, mapping));
	}

}
