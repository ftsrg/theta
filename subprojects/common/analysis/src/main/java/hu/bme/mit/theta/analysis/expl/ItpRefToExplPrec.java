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
package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

public class ItpRefToExplPrec implements RefutationToPrec<ExplPrec, ItpRefutation> {

	@Override
	public ExplPrec toPrec(final ItpRefutation refutation, final int index) {
		final Expr<BoolType> expr = refutation.get(index);
		final Collection<VarDecl<?>> vars = ExprUtils.getVars(expr);
		final ExplPrec prec = ExplPrec.of(vars);
		return prec;
	}

	@Override
	public ExplPrec join(final ExplPrec prec1, final ExplPrec prec2) {
		checkNotNull(prec1);
		checkNotNull(prec2);
		return prec1.join(prec2);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
