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
package hu.bme.mit.theta.xsts.analysis.concretizer;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.XstsAction;
import hu.bme.mit.theta.xsts.analysis.XstsState;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

public final class XstsTraceConcretizerUtil {

    private XstsTraceConcretizerUtil() {
    }

    public static XstsStateSequence concretize(
            final Trace<XstsState<?>, XstsAction> trace, SolverFactory solverFactory, final XSTS xsts) {

        final VarFilter varFilter = VarFilter.of(xsts);
        final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(
                xsts.getInitFormula(),
                Not(xsts.getProp()), solverFactory.createItpSolver());
        final ExprTraceStatus<ItpRefutation> status = checker.check(trace);
        checkArgument(status.isFeasible(), "Infeasible trace.");
        final Trace<Valuation, ? extends Action> valuations = status.asFeasible().getValuations();

        assert valuations.getStates().size() == trace.getStates().size();

        final List<XstsState<ExplState>> xstsStates = new ArrayList<>();
        for (int i = 0; i < trace.getStates().size(); ++i) {
            xstsStates.add(XstsState.of(ExplState.of(varFilter.filter(valuations.getState(i))),
                    trace.getState(i).lastActionWasEnv(), trace.getState(i).isInitialized()));
        }

        return XstsStateSequence.of(xstsStates, xsts);
    }
}