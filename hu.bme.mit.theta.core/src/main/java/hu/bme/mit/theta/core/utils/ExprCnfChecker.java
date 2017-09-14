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

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;

final class ExprCnfChecker {

	private static enum CnfStatus {
		START(0), INSIDE_AND(1), INSIDE_OR(2), INSIDE_NOT(3);
		final int value;

		private CnfStatus(final int value) {
			this.value = value;
		}
	}

	static boolean isExprCnf(final Expr<BoolType> expr) {
		return isExprCnf(expr, CnfStatus.START);
	}

	private static boolean isExprCnf(final Expr<BoolType> expr, final CnfStatus status) {
		if (expr instanceof BoolLitExpr) {
			return true;

		} else if (expr instanceof NotExpr) {
			final NotExpr notExpr = (NotExpr) expr;
			// NOT is not allowed inside NOT
			if (status.value >= CnfStatus.INSIDE_NOT.value) {
				return false;
			} else {
				return isExprCnf(notExpr.getOp(), CnfStatus.INSIDE_NOT);
			}

		} else if (expr instanceof AndExpr) {
			final AndExpr andExpr = (AndExpr) expr;
			// AND is allowed inside AND
			if (status.value > CnfStatus.INSIDE_AND.value) {
				return false;
			} else {
				return andExpr.getOps().stream().allMatch(op -> isExprCnf(op, CnfStatus.INSIDE_AND));
			}

		} else if (expr instanceof OrExpr) {
			final OrExpr orExpr = (OrExpr) expr;
			// OR is allowed inside OR
			if (status.value > CnfStatus.INSIDE_OR.value) {
				return false;
			} else {
				return orExpr.getOps().stream().allMatch(op -> isExprCnf(op, CnfStatus.INSIDE_OR));
			}

		} else if (expr instanceof ImplyExpr) {
			return false;

		} else if (expr instanceof IffExpr) {
			return false;

		} else if (expr instanceof RefExpr) {
			return true;

		} else if (expr instanceof PrimeExpr) {
			final PrimeExpr<BoolType> primeExpr = (PrimeExpr<BoolType>) expr;
			return isExprCnf(primeExpr.getOp(), CnfStatus.INSIDE_NOT);

		} else if (expr instanceof IteExpr) {
			return false;

		} else {
			return true;
		}
	}
}
