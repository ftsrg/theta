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
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class EqExpr<OpType extends Equational<OpType>> extends BinaryExpr<OpType, BoolType> {

	protected EqExpr(final Expr<OpType> leftOp, final Expr<OpType> rightOp) {
		super(leftOp, rightOp);
	}

	public static <OpType extends Equational<OpType>> EqExpr<?> create2(final Expr<?> leftOp, final Expr<?> rightOp) {
		@SuppressWarnings("unchecked") final OpType type = (OpType) leftOp.getType();
		final Expr<OpType> newLeftOp = cast(leftOp, type);
		final Expr<OpType> newRightOp = cast(rightOp, type);
		return type.Eq(newLeftOp, newRightOp);
	}

}
