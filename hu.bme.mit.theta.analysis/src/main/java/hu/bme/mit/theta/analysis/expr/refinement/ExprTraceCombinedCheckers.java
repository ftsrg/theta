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
package hu.bme.mit.theta.analysis.expr.refinement;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.ItpSolver;

public final class ExprTraceCombinedCheckers {

	public static ExprTraceChecker<ItpRefutation> createBwFwMinPrune(final Expr<BoolType> init,
			final Expr<BoolType> target, final ItpSolver solver) {
		final ExprTraceBwBinItpChecker bwChecker = ExprTraceBwBinItpChecker.create(init, target, solver);
		final ExprTraceFwBinItpChecker fwChecker = ExprTraceFwBinItpChecker.create(init, target, solver);
		final ExprTraceStatusMerger<ItpRefutation> merger = ExprTraceStatusMergers.minPruneIndex();
		return ExprTraceCombinedChecker.create(bwChecker, fwChecker, merger);
	}

	public static ExprTraceChecker<ItpRefutation> createBwFwMaxPrune(final Expr<BoolType> init,
			final Expr<BoolType> target, final ItpSolver solver) {
		final ExprTraceBwBinItpChecker bwChecker = ExprTraceBwBinItpChecker.create(init, target, solver);
		final ExprTraceFwBinItpChecker fwChecker = ExprTraceFwBinItpChecker.create(init, target, solver);
		final ExprTraceStatusMerger<ItpRefutation> merger = ExprTraceStatusMergers.maxPruneIndex();
		return ExprTraceCombinedChecker.create(bwChecker, fwChecker, merger);
	}
}
