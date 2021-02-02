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
package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;

import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public abstract class PosExpr<ExprType extends Additive<ExprType>> extends UnaryExpr<ExprType, ExprType> {

	protected PosExpr(final Expr<ExprType> op) {
		super(op);
	}

	public static <ExprType extends Additive<ExprType>> PosExpr<?> create2(final Expr<?> op) {
		@SuppressWarnings("unchecked") final ExprType type = (ExprType) op.getType();
		final Expr<ExprType> newOp = cast(op, type);
		return type.Pos(newOp);
	}

}
