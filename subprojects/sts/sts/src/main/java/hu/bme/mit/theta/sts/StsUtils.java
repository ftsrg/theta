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
package hu.bme.mit.theta.sts;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

/**
 * Utilities related to the STS formalism.
 */
public final class StsUtils {
	private StsUtils() {
	}

	/**
	 * Transform STS into an equivalent new STS, without if-then-else
	 * constructs.
	 *
	 * @param sts Original STS
	 * @return Transformed STS
	 */
	public static STS eliminateIte(final STS sts) {
		final STS.Builder builder = STS.builder();
		builder.addInit(ExprUtils.eliminateIte(sts.getInit()));
		builder.addTrans(ExprUtils.eliminateIte(sts.getTrans()));
		builder.setProp(ExprUtils.eliminateIte(sts.getProp()));
		return builder.build();
	}

	/**
	 * Transform STS into a new STS, where the initial and transition formula is
	 * in an equisatisfiable CNF form. The property is not transformed (as it
	 * may be negated).
	 *
	 * @param sts Original STS
	 * @return Transformed STS
	 */
	public static STS transformToCnf(final STS sts) {
		final STS.Builder builder = STS.builder();
		builder.addInit(transformIfNonCNF(sts.getInit()));
		builder.addTrans(transformIfNonCNF(sts.getTrans()));
		builder.setProp(sts.getProp());
		return builder.build();
	}

	private static Expr<BoolType> transformIfNonCNF(final Expr<BoolType> expr) {
		if (ExprUtils.isExprCnf(expr)) {
			return expr;
		} else {
			return ExprUtils.transformEquiSatCnf(expr);
		}
	}
}
