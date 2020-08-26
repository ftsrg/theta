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
package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

final class BasicExprState implements ExprState {

	private final Expr<BoolType> expr;

	private BasicExprState(final Expr<BoolType> expr) {
		this.expr = checkNotNull(expr);
	}

	public static BasicExprState of(final Expr<BoolType> expr) {
		return new BasicExprState(expr);
	}

	@Override
	public Expr<BoolType> toExpr() {
		return expr;
	}

	@Override
	public boolean isBottom() {
		return expr.equals(False());
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).body().add(expr).toString();
	}
}
