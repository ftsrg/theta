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

import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;

public abstract class SubExpr<ExprType extends Additive<ExprType>> extends BinaryExpr<ExprType, ExprType> {

	protected SubExpr(final Expr<ExprType> leftOp, final Expr<ExprType> rightOp) {
		super(leftOp, rightOp);
	}

	public static <ExprType extends Additive<ExprType>> SubExpr<?> create2(final Expr<?> leftOp, final Expr<?> rightOp) {
		@SuppressWarnings("unchecked") final ExprType type = (ExprType) leftOp.getType();
		final Expr<ExprType> newLeftOp = cast(leftOp, type);
		final Expr<ExprType> newRightOp = cast(rightOp, type);
		return type.Sub(newLeftOp, newRightOp);
	}

}
