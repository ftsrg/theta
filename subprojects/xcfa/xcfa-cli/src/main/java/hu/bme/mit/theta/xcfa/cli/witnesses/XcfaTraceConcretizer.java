/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.ptr.PtrState;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import java.util.*;
import java.util.stream.Collectors;
import kotlin.Triple;

/**
 * Similar to CfaTraceConcretizer Takes a trace given by an unsafe result and uses and SMT solver to
 * output a concrete counterexample
 */
public class XcfaTraceConcretizer {
    public static Trace<XcfaState<ExplState>, XcfaAction> concretize(
            final Trace<XcfaState<PtrState<?>>, XcfaAction> trace,
            SolverFactory solverFactory,
            ParseContext parseContext) {
        List<XcfaState<PtrState<?>>> sbeStates = new ArrayList<>();
        List<XcfaAction> sbeActions = new ArrayList<>();

        sbeStates.add(trace.getState(0).withState(new PtrState<>(ExplState.top())));

        Map<Type, List<Triple<Expr<?>, Expr<?>, Expr<IntType>>>> nextW = Collections.emptyMap();
        for (int i = 0; i < trace.getActions().size(); ++i) {
            final XcfaEdge edge =
                    new XcfaEdge(
                            trace.getAction(i).getSource(),
                            trace.getAction(i).getTarget(),
                            trace.getAction(i).getLabel(),
                            trace.getAction(i).getEdge().getMetadata());
            final XcfaAction action =
                    new XcfaAction(
                            trace.getAction(i).getPid(),
                            edge,
                            nextW,
                            trace.getAction(i).getInCnt());
            sbeActions.add(action);
            nextW = action.nextWriteTriples();
            sbeStates.add(trace.getState(i + 1).withState(new PtrState<>(ExplState.top())));
        }
        Trace<XcfaState<?>, XcfaAction> sbeTrace = Trace.of(sbeStates, sbeActions);
        final ExprTraceChecker<ItpRefutation> checker =
                ExprTraceFwBinItpChecker.create(
                        BoolExprs.True(), BoolExprs.True(), solverFactory.createItpSolver());
        final ExprTraceStatus<ItpRefutation> status = checker.check(sbeTrace);
        checkArgument(status.isFeasible(), "Infeasible trace.");
        final Trace<Valuation, ? extends Action> valuations = status.asFeasible().getValuations();

        assert valuations.getStates().size() == sbeTrace.getStates().size();

        final List<XcfaState<ExplState>> cfaStates = new ArrayList<>();
        final Set<VarDecl<?>> varSoFar = new LinkedHashSet<>();
        for (int i = 0; i < sbeTrace.getStates().size(); ++i) {
            cfaStates.add(
                    new XcfaState<>(
                            sbeTrace.getState(i).getXcfa(),
                            sbeTrace.getState(i).getProcesses(),
                            ExplState.of(
                                    ImmutableValuation.from(
                                            valuations.getState(i).toMap().entrySet().stream()
                                                    .filter(it -> varSoFar.contains(it.getKey()))
                                                    .collect(
                                                            Collectors.toMap(
                                                                    Map.Entry<Decl<?>, LitExpr<?>>
                                                                            ::getKey,
                                                                    Map.Entry::getValue))))));
            if (i < sbeTrace.getActions().size()) {
                varSoFar.addAll(ExprUtils.getVars(sbeTrace.getAction(i).toExpr()));
            }
        }

        return Trace.of(cfaStates, sbeActions);
    }
}
