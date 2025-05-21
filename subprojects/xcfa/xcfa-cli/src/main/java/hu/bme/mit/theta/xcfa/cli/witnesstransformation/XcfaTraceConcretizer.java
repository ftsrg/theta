/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.cli.witnesstransformation;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.c2xcfa.CMetaDataKt.getCMetaData;
import static hu.bme.mit.theta.xcfa.UtilsKt.getFlatLabels;

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
import hu.bme.mit.theta.xcfa.model.*;
import java.util.*;
import java.util.stream.Collectors;
import kotlin.Triple;

/**
 * Similar to CfaTraceConcretizer Takes a trace given by an unsafe result and uses and SMT solver to
 * output a concrete counterexample
 */
public class XcfaTraceConcretizer {
    public static Trace<XcfaState<ExplState>, XcfaAction> concretize(
            Trace<XcfaState<PtrState<?>>, XcfaAction> trace,
            SolverFactory solverFactory,
            ParseContext parseContext) {

        trace =
                Trace.of(
                        trace.getStates().stream()
                                .map(
                                        ptrStateXcfaState ->
                                                ptrStateXcfaState.getSGlobal().getInnerState()
                                                                instanceof ExplState explState
                                                        ? ptrStateXcfaState.withState(
                                                                new PtrState(
                                                                        ExplState.of(
                                                                                ImmutableValuation
                                                                                        .from(
                                                                                                explState
                                                                                                        .toMap()
                                                                                                        .entrySet()
                                                                                                        .stream()
                                                                                                        .filter(
                                                                                                                declLitExprEntry ->
                                                                                                                        parseContext
                                                                                                                                .getMetadata()
                                                                                                                                .getMetadataValue(
                                                                                                                                        declLitExprEntry
                                                                                                                                                .getKey()
                                                                                                                                                .getName(),
                                                                                                                                        "cName")
                                                                                                                                .isPresent())
                                                                                                        .collect(
                                                                                                                Collectors
                                                                                                                        .toMap(
                                                                                                                                Map
                                                                                                                                                .Entry
                                                                                                                                        ::getKey,
                                                                                                                                Map
                                                                                                                                                .Entry
                                                                                                                                        ::getValue))))))
                                                        : ptrStateXcfaState)
                                .toList(),
                        trace.getActions());

        List<XcfaState<PtrState<?>>> sbeStates = new ArrayList<>();
        List<XcfaAction> sbeActions = new ArrayList<>();

        sbeStates.add(trace.getState(0));

        Map<Type, List<Triple<Expr<?>, Expr<?>, Expr<IntType>>>> nextW = Collections.emptyMap();
        final XcfaLocation placeholder =
                new XcfaLocation("__THETA__placeholder__", EmptyMetaData.INSTANCE);
        for (int i = 0; i < trace.getActions().size(); ++i) {
            final var action = trace.getAction(i);
            var labels = getFlatLabels(action.getLabel());
            final var groupedLabels = new ArrayList<XcfaLabel>();
            var currentList = new ArrayList<XcfaLabel>();
            for (XcfaLabel label : labels) {
                if (currentList.isEmpty()) {
                    currentList.add(label);
                } else {
                    final var otherMetadata = getCMetaData(currentList.get(0));
                    final var otherAstNodes =
                            otherMetadata == null ? List.of() : otherMetadata.getAstNodes();
                    final var metadata = getCMetaData(label);
                    final var astNodes = metadata == null ? List.of() : metadata.getAstNodes();
                    if (otherAstNodes.equals(astNodes)) {
                        currentList.add(label);
                    } else {
                        if (currentList.size() == 1) {
                            groupedLabels.add(currentList.get(0));
                        } else {
                            groupedLabels.add(
                                    new SequenceLabel(
                                            List.copyOf(currentList),
                                            currentList.get(0).getMetadata()));
                        }
                        currentList.clear();
                        currentList.add(label);
                    }
                }
            }
            if (currentList.size() == 1) {
                groupedLabels.add(currentList.get(0));
            } else if (currentList.size() > 1) {
                groupedLabels.add(
                        new SequenceLabel(
                                List.copyOf(currentList), currentList.get(0).getMetadata()));
            }
            labels = groupedLabels;
            for (int j = 0; j < labels.size(); j++) {
                final XcfaLocation source = j == 0 ? action.getSource() : placeholder;
                final XcfaLocation target =
                        j == labels.size() - 1 ? action.getTarget() : placeholder;
                final XcfaLabel label = labels.get(j);
                final MetaData metadata = label.getMetadata();
                final XcfaState<PtrState<?>> nextState =
                        j == labels.size() - 1
                                ? trace.getState(i + 1)
                                : trace.getState(i + 1)
                                        .withLocation(action.getPid(), placeholder)
                                        .withState(new PtrState<>(ExplState.top(), 0));

                final XcfaEdge edge = new XcfaEdge(source, target, label, metadata);
                final XcfaAction newAction =
                        new XcfaAction(action.getPid(), edge, nextW, action.getInCnt());
                sbeActions.add(newAction);
                nextW = newAction.nextWriteTriples();
                sbeStates.add(nextState);
            }
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
                                                    .filter(
                                                            it ->
                                                                    varSoFar.contains(it.getKey())
                                                                            && parseContext
                                                                                    .getMetadata()
                                                                                    .getMetadataValue(
                                                                                            it.getKey()
                                                                                                    .getName(),
                                                                                            "cName")
                                                                                    .isPresent())
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
