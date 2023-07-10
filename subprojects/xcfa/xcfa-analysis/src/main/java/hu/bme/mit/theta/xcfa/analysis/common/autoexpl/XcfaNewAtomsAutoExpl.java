/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis.common.autoexpl;

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.NewAtomsAutoExpl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.utils.XcfaUtils;

import java.util.Set;
import java.util.stream.Collectors;

public class XcfaNewAtomsAutoExpl implements XcfaAutoExpl {
	@Override
	public AutoExpl create(XCFA xcfa) {
		final Set<Expr<BoolType>> atoms = XcfaUtils.getAtoms(xcfa);

		final Set<Expr<BoolType>> canonicalAtoms = atoms.stream()
				.map(ExprUtils::canonize)
				.flatMap(atom -> ExprUtils.getAtoms(atom).stream())
				.collect(Collectors.toSet());
		return new NewAtomsAutoExpl(Set.of(), canonicalAtoms, 0);
	}
}
