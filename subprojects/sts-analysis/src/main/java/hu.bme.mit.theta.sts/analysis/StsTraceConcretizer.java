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
package hu.bme.mit.theta.sts.analysis;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.sts.STS;

public final class StsTraceConcretizer {
	private StsTraceConcretizer() {
	}

	public static Trace<Valuation, StsAction> concretize(
			final STS sts, final Trace<ExprState, StsAction> trace, final SolverFactory solverFactory) {
		final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(sts.getInit(),
				BoolExprs.Not(sts.getProp()), solverFactory.createItpSolver());
		final ExprTraceStatus<ItpRefutation> status = checker.check(trace);
		checkArgument(status.isFeasible(), "Infeasible trace.");
		final Trace<Valuation, ? extends Action> valuations = status.asFeasible().getValuations();

		assert valuations.getStates().size() == trace.getStates().size();

		return Trace.of(valuations.getStates(), trace.getActions());
	}
}
