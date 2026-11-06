/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
import static hu.bme.mit.theta.xcfa.utils.AccessUtilsKt.collectVarsWithAccessType;
import static hu.bme.mit.theta.xcfa.utils.AccessUtilsKt.getDereferences;
import static hu.bme.mit.theta.xcfa.utils.AccessUtilsKt.isWritten;
import static hu.bme.mit.theta.xcfa.utils.UtilsKt.getFlatLabels;

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
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.fptype.FpExprs;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.statements.CCall;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.*;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import kotlin.Triple;

/**
 * Similar to CfaTraceConcretizer Takes a trace given by an unsafe result and uses and SMT solver to
 * output a concrete counterexample
 */
public class XcfaTraceConcretizer {

    /**
     * Reverse map (renamed/SSA variable -> original declaration) over all of `state`'s processes.
     */
    protected Map<VarDecl<?>, VarDecl<?>> revLookup(XcfaState<?> state) {
        final var revLookup = new LinkedHashMap<VarDecl<?>, VarDecl<?>>();
        state.getProcesses().values().stream()
                .flatMap(process -> process.getVarLookup().stream())
                .flatMap(lookup -> lookup.entrySet().stream())
                .forEach(entry -> revLookup.put(entry.getValue(), entry.getKey()));
        return revLookup;
    }

    /** Whether `decl` corresponds to a named C variable (carries a `cName` metadata entry). */
    protected boolean isProgramVar(VarDecl<?> decl, ParseContext parseContext) {
        return parseContext.getMetadata().getMetadataValue(decl.getName(), "cName").isPresent();
    }

    protected boolean isSbe(XcfaLabel label) {
        final var otherMetadata = getCMetaData(label);
        final var otherAstNodes = otherMetadata == null ? List.of() : otherMetadata.getAstNodes();
        final var metadata = getCMetaData(label);
        final var astNodes = metadata == null ? List.of() : metadata.getAstNodes();
        return otherAstNodes.equals(astNodes);
    }

    /**
     * Rebuild `state`'s global valuation keeping only variables that map back to a named C
     * variable, so the re-checked trace carries just the C-visible state.
     */
    protected XcfaState<PtrState<?>> keepProgramVars(
            XcfaState<PtrState<?>> state, ParseContext parseContext) {
        if (!(state.getSGlobal().getInnerState() instanceof ExplState explState)) {
            return state;
        }
        final var revLookup = revLookup(state);
        final var kept =
                explState.toMap().entrySet().stream()
                        .filter(
                                entry -> {
                                    final var decl = (VarDecl<?>) entry.getKey();
                                    return isProgramVar(
                                            revLookup.getOrDefault(decl, decl), parseContext);
                                })
                        .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
        return state.withState(new PtrState<>(ExplState.of(ImmutableValuation.from(kept))));
    }

    /**
     * The concrete `ExplState` for a trace state: the model `valuation` restricted to variables
     * already written (`varSoFar`) that are either a kept nondet result (`nondetVars`) or map back
     * to a named C variable.
     */
    protected ExplState concreteState(
            XcfaState<?> state,
            Valuation valuation,
            Set<VarDecl<?>> varSoFar,
            Set<VarDecl<?>> nondetVars,
            ParseContext parseContext) {
        final var revLookup = revLookup(state);
        final var kept =
                valuation.toMap().entrySet().stream()
                        .filter(
                                entry -> {
                                    final var decl = (VarDecl<?>) entry.getKey();
                                    return varSoFar.contains(decl)
                                            && (nondetVars.contains(decl)
                                                    || isProgramVar(decl, parseContext)
                                                    || isProgramVar(
                                                            revLookup.getOrDefault(decl, decl),
                                                            parseContext));
                                })
                        .collect(
                                Collectors.toMap(
                                        Map.Entry<Decl<?>, LitExpr<?>>::getKey,
                                        Map.Entry::getValue));
        return ExplState.of(ImmutableValuation.from(kept));
    }

    public Trace<XcfaState<ExplState>, XcfaAction> concretize(
            Trace<XcfaState<PtrState<?>>, XcfaAction> trace,
            SolverFactory solverFactory,
            ParseContext parseContext) {
        return concretize(trace, solverFactory, parseContext, Function.identity());
    }

    public Trace<XcfaState<ExplState>, XcfaAction> concretize(
            Trace<XcfaState<PtrState<?>>, XcfaAction> trace,
            SolverFactory solverFactory,
            ParseContext parseContext,
            Function<ExprTraceChecker<ItpRefutation>, ExprTraceChecker<ItpRefutation>>
                    exprTraceCheckerWrapper) {
        final Trace<XcfaState<?>, XcfaAction> sbeTrace =
                splitLabels(keepNamedVars(trace, parseContext)).trace();
        final ExprTraceChecker<ItpRefutation> checker =
                exprTraceCheckerWrapper.apply(
                        ExprTraceFwBinItpChecker.create(
                                BoolExprs.True(),
                                BoolExprs.True(),
                                solverFactory.createItpSolver()));
        final ExprTraceStatus<ItpRefutation> status = checker.check(sbeTrace);
        checkArgument(status.isFeasible(), "Infeasible trace.");
        return toConcreteTrace(
                sbeTrace, status.asFeasible().getValuations().getStates(), parseContext);
    }

    /** A concrete lasso: the state at `cycleStart` equals the last state of the trace. */
    public record ConcreteLasso(Trace<XcfaState<ExplState>, XcfaAction> trace, int cycleStart) {}

    /**
     * Concretizes a termination counterexample so that its cycle can repeat forever. Each earlier
     * visit of the last state's locations is tried as the start of the cycle, the latest first.
     * Returns null if none of them repeats the state, or if the trace uses pointer dereferences, as
     * the variables then do not hold the whole state.
     */
    public ConcreteLasso concretizeLasso(
            Trace<XcfaState<PtrState<?>>, XcfaAction> trace,
            SolverFactory solverFactory,
            ParseContext parseContext) {
        final SplitTrace split = splitLabels(keepNamedVars(trace, parseContext));
        final Trace<XcfaState<?>, XcfaAction> sbeTrace = split.trace();
        if (sbeTrace.getActions().stream()
                .anyMatch(action -> !getDereferences(action.getLabel()).isEmpty())) {
            return null;
        }
        final Solver solver = solverFactory.createSolver();
        final List<VarIndexing> indexings = new ArrayList<>();
        indexings.add(VarIndexingFactory.indexing(0));
        solver.add(PathUtils.unfold(sbeTrace.getState(0).toExpr(), indexings.get(0)));
        for (int i = 1; i < sbeTrace.getStates().size(); ++i) {
            final XcfaAction action = sbeTrace.getAction(i - 1);
            indexings.add(indexings.get(i - 1).add(action.nextIndexing()));
            solver.add(PathUtils.unfold(sbeTrace.getState(i).toExpr(), indexings.get(i)));
            solver.add(PathUtils.unfold(action.toExpr(), indexings.get(i - 1)));
        }
        final VarIndexing end = indexings.get(indexings.size() - 1);
        final int last = trace.getStates().size() - 1;
        for (int k = last - 1; k >= 0; --k) {
            if (!sameLocations(trace.getState(k), trace.getState(last))) {
                continue;
            }
            final int start = split.positions().get(k);
            final List<XcfaAction> cycle =
                    sbeTrace.getActions().subList(start, sbeTrace.getActions().size());
            try (var wpp = new WithPushPop(solver)) {
                for (VarDecl<?> decl : writtenVars(cycle, sbeTrace.getState(0).getXcfa())) {
                    solver.add(
                            sameValue(
                                    PathUtils.unfold(decl.getRef(), indexings.get(start)),
                                    PathUtils.unfold(decl.getRef(), end)));
                }
                if (solver.check().isSat()) {
                    final Valuation model = solver.getModel();
                    final List<Valuation> valuations =
                            indexings.stream()
                                    .map(indexing -> PathUtils.extractValuation(model, indexing))
                                    .toList();
                    return new ConcreteLasso(
                            toConcreteTrace(sbeTrace, valuations, parseContext), start);
                }
            }
        }
        return null;
    }

    private boolean sameLocations(XcfaState<?> a, XcfaState<?> b) {
        return a.getProcesses().keySet().equals(b.getProcesses().keySet())
                && a.getProcesses().entrySet().stream()
                        .allMatch(
                                e ->
                                        e.getValue()
                                                .getLocs()
                                                .equals(
                                                        b.getProcesses()
                                                                .get(e.getKey())
                                                                .getLocs()));
    }

    private Set<VarDecl<?>> writtenVars(List<XcfaAction> actions, XCFA xcfa) {
        final Set<VarDecl<?>> vars = new LinkedHashSet<>();
        for (XcfaAction action : actions) {
            for (XcfaLabel label : getFlatLabels(action.getLabel())) {
                collectVarsWithAccessType(label, xcfa)
                        .forEach(
                                (decl, access) -> {
                                    if (isWritten(access)) vars.add(decl);
                                });
            }
        }
        return vars;
    }

    @SuppressWarnings("unchecked")
    private Expr<BoolType> sameValue(Expr<?> a, Expr<?> b) {
        return a.getType() instanceof FpType
                ? FpExprs.FpAssign((Expr<FpType>) a, (Expr<FpType>) b)
                : AbstractExprs.Eq(a, b);
    }

    private Trace<XcfaState<PtrState<?>>, XcfaAction> keepNamedVars(
            Trace<XcfaState<PtrState<?>>, XcfaAction> trace, ParseContext parseContext) {
        return Trace.of(
                trace.getStates().stream()
                        .map(state -> keepProgramVars(state, parseContext))
                        .toList(),
                trace.getActions());
    }

    /**
     * The trace with one action per C statement. `positions` holds the index of each state of
     * `trace` in the result.
     */
    private record SplitTrace(Trace<XcfaState<?>, XcfaAction> trace, List<Integer> positions) {}

    private SplitTrace splitLabels(Trace<XcfaState<PtrState<?>>, XcfaAction> trace) {
        List<XcfaState<PtrState<?>>> sbeStates = new ArrayList<>();
        List<XcfaAction> sbeActions = new ArrayList<>();
        List<Integer> positions = new ArrayList<>();

        sbeStates.add(trace.getState(0));
        positions.add(0);

        Map<Type, List<Triple<Expr<?>, Expr<?>, Expr<IntType>>>> nextW = Collections.emptyMap();
        final XcfaLocation placeholder =
                new XcfaLocation("__THETA__placeholder__", EmptyMetaData.INSTANCE);
        int nextCount = 0;
        for (int i = 0; i < trace.getActions().size(); ++i) {
            final var action = trace.getAction(i);
            var labels = getFlatLabels(action.getLabel());
            final var groupedLabels = new ArrayList<XcfaLabel>();
            var currentList = new ArrayList<XcfaLabel>();
            for (XcfaLabel label : labels) {
                if (currentList.isEmpty()) {
                    currentList.add(label);
                } else {
                    if (isSbe(currentList.get(0))) {
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
            if (labels.isEmpty()) {
                labels = List.of(NopLabel.INSTANCE);
            }

            for (int j = 0; j < labels.size(); j++) {
                final XcfaLocation source = j == 0 ? action.getSource() : placeholder;
                final XcfaLocation target =
                        j == labels.size() - 1 ? action.getTarget() : placeholder;
                XcfaLabel label = labels.get(j);
                // The OC encoding writes the spawned thread's id into the (opaque) pthread_t handle
                // at the start, but StartLabel.toStmt() is a no-op, so the sequential re-check
                // would
                // freeze the handle at its zero initializer and contradict that thread-id write.
                // Havoc the handle here so it stays the opaque value the trace assigns it.
                if (label instanceof StartLabel) {
                    label =
                            new StmtLabel(
                                    HavocStmt.of(((StartLabel) label).getPidVar()),
                                    ChoiceType.NONE,
                                    label.getMetadata());
                }
                final MetaData metadata =
                        label.getMetadata() == EmptyMetaData.INSTANCE
                                ? action.getEdge().getMetadata()
                                : label.getMetadata();
                final XcfaState<PtrState<?>> nextState =
                        j == labels.size() - 1
                                ? trace.getState(i + 1)
                                : trace.getState(i + 1)
                                        .withLocation(action.getPid(), placeholder)
                                        .withState(new PtrState<>(ExplState.top(), 0));

                final XcfaEdge edge = new XcfaEdge(source, target, label, metadata);
                final XcfaAction newAction =
                        new XcfaAction(action.getPid(), edge, nextW, nextCount);
                sbeActions.add(newAction);
                nextW = newAction.nextWriteTriples();
                sbeStates.add(nextState);
                nextCount =
                        newAction.getCnts().values().stream()
                                .max(Comparator.naturalOrder())
                                .orElse(nextCount);
            }
            positions.add(sbeStates.size() - 1);
        }
        return new SplitTrace(Trace.of(sbeStates, sbeActions), positions);
    }

    private Trace<XcfaState<ExplState>, XcfaAction> toConcreteTrace(
            Trace<XcfaState<?>, XcfaAction> sbeTrace,
            List<? extends Valuation> valuations,
            ParseContext parseContext) {
        assert valuations.size() == sbeTrace.getStates().size();

        final List<XcfaState<ExplState>> cfaStates = new ArrayList<>();
        final Set<VarDecl<?>> varSoFar = new LinkedHashSet<>();
        // result variables of __VERIFIER_nondet_* calls: these are internal temporaries without a
        // cName, but their concrete values are needed to emit function_return witness waypoints, so
        // they are kept in the concretized state even though they are filtered out otherwise.
        final Set<VarDecl<?>> nondetVars = new LinkedHashSet<>();
        for (int i = 0; i < sbeTrace.getStates().size(); ++i) {
            cfaStates.add(
                    new XcfaState<>(
                            sbeTrace.getState(i).getXcfa(),
                            sbeTrace.getState(i).getProcesses(),
                            concreteState(
                                    sbeTrace.getState(i),
                                    valuations.get(i),
                                    varSoFar,
                                    nondetVars,
                                    parseContext)));
            if (i < sbeTrace.getActions().size()) {
                for (XcfaLabel flatLabel : getFlatLabels(sbeTrace.getAction(i).getLabel())) {
                    //                    if (flatLabel.getMetadata().isSubstantial()) {
                    var accesses =
                            collectVarsWithAccessType(flatLabel, sbeTrace.getState(i).getXcfa());
                    final var written =
                            accesses.entrySet().stream()
                                    .filter(it -> isWritten(it.getValue()))
                                    .map(it -> it.getKey())
                                    .toList();
                    varSoFar.addAll(written);
                    // the havoc replacing a __VERIFIER_nondet_* call carries the call's CMetaData;
                    // its written variable is the nondet result and must be kept (see nondetVars).
                    final var meta = getCMetaData(flatLabel);
                    if (meta != null
                            && meta.getAstNodes().stream()
                                    .anyMatch(
                                            n ->
                                                    n instanceof CCall cc
                                                            && cc.getFunctionId()
                                                                    .contains(
                                                                            "__VERIFIER_nondet_"))) {
                        nondetVars.addAll(written);
                    }
                    //                    }
                }
            }
        }

        return Trace.of(cfaStates, sbeTrace.getActions());
    }
}
