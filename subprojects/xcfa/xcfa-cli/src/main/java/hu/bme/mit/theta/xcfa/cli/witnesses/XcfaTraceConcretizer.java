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

package hu.bme.mit.theta.xcfa.cli.witnesses;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;

/**
 * Similar to CfaTraceConcretizer
 * Takes a trace given by an unsafe result and uses and SMT solver to output a concrete counterexample
 */
public class XcfaTraceConcretizer {
    public static Trace<XcfaState<ExplState>, XcfaAction> concretize(
            final Trace<XcfaState<?>, XcfaAction> trace, SolverFactory solverFactory) {
        List<XcfaState<?>> sbeStates = new ArrayList<>();
        List<XcfaAction> sbeActions = new ArrayList<>();

        sbeStates.add(trace.getState(0));
        for (int i = 0; i < trace.getActions().size(); ++i) {
            final XcfaEdge edge = new XcfaEdge(trace.getAction(i).getSource(), trace.getAction(i).getTarget(), trace.getAction(i).getLabel());
            sbeActions.add(new XcfaAction(trace.getAction(i).getPid(), edge));
            sbeStates.add(trace.getState(i + 1));
        }
        Trace<XcfaState<?>, XcfaAction> sbeTrace = Trace.of(sbeStates, sbeActions);
        final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(BoolExprs.True(),
                BoolExprs.True(), solverFactory.createItpSolver());
        final ExprTraceStatus<ItpRefutation> status = checker.check(sbeTrace);
        checkArgument(status.isFeasible(), "Infeasible trace.");
        final Trace<Valuation, ? extends Action> valuations = status.asFeasible().getValuations();

        assert valuations.getStates().size() == sbeTrace.getStates().size();

        final List<XcfaState<ExplState>> cfaStates = new ArrayList<>();
        for (int i = 0; i < sbeTrace.getStates().size(); ++i) {
            cfaStates.add(new XcfaState<>(null, sbeTrace.getState(i).getProcesses(), ExplState.of(valuations.getState(i))));
        }

        return Trace.of(cfaStates, sbeTrace.getActions());
    }

}