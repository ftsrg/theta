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
package hu.bme.mit.theta.analysis.algorithm.ic3;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.EmptyProof;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExprKt;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import org.jspecify.annotations.Nullable;

import java.util.*;

public class Ic3Checker
        implements SafetyChecker<EmptyProof, Trace<ExplState, ExprAction>, UnitPrec> {
    private final MonolithicExpr monolithicExpr;
    private final List<Frame> frames;
    private final SolverFactory solverFactory;
    private final UCSolver solver;
    private final IC3Optimizations optimizations;
    private int currentFrameNumber;
    private final Logger logger;

    public Ic3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory, Logger logger) {
        this(monolithicExpr, solverFactory, new IC3Optimizations(true,true,true,true, true,true,true), logger);
    }

    public Ic3Checker(
        MonolithicExpr monolithicExpr,
        SolverFactory solverFactory, IC3Optimizations optimizations,
        Logger logger) {
        this.monolithicExpr = monolithicExpr;
        this.optimizations = optimizations;
        this.logger = logger;
        this.solverFactory = solverFactory;
        frames = new ArrayList<>();
        solver = solverFactory.createUCSolver();
        frames.add(new Frame(null, solver, monolithicExpr, optimizations));
        currentFrameNumber = 0;
    }

    @Override
    public SafetyResult<EmptyProof, Trace<ExplState, ExprAction>> check(UnitPrec prec) {
        // check if init violates prop
        var firstTrace = checkFirst();
        if (firstTrace != null) {
            return SafetyResult.unsafe(firstTrace, EmptyProof.getInstance());
        }
        while (true) {
            final ProofObligation counterExample = checkCurrentFrameForInterSections(Not(monolithicExpr.getPropExpr()));
            if (counterExample != null) {
                var proofObligationsList = tryBlock(counterExample);
                if (proofObligationsList != null) {
                    var trace = makeTrace(proofObligationsList);
                    return SafetyResult.unsafe(trace, EmptyProof.getInstance());
                }
            } else {
                if (propagate()) {
                    return SafetyResult.safe(EmptyProof.getInstance());
                }
            }
        }
    }

    private Set<Expr<BoolType>> convertValuationToExpression(Valuation model) {
        if (model != null) {
            return new HashSet<>(getConjuncts(PathUtils.foldin(filterModel(model).toExpr(), 0)));
        } else {
            return null;
        }
    }
    private Valuation filterModel(Valuation model) {
        return PathUtils.extractValuation(
            model,
            VarIndexingFactory.indexing(0),
            monolithicExpr.getVars());
    }

    private MutableValuation removeRedundantVariables(Valuation model, ProofObligation proofObligation) {

        final MutableValuation filteredModel = new MutableValuation();
        monolithicExpr.getVars().stream()
            .map(varDecl -> varDecl.getConstDecl(0))
            .filter(model.toMap()::containsKey)
            .forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
        var vars = new HashSet<>(filteredModel.toMap().keySet());
        for (var var : vars) {
            if (!(var.getType() instanceof BoolType)) {
                continue;
            }
            var origValue = model.eval(var).get();
            var negatedValue =
                BoolLitExpr.of(!((BoolLitExpr) origValue).getValue());
            filteredModel.put(var, negatedValue);
            //todo use push/pop
            try (var wpp2 = new WithPushPop(solver)) {
                var a = PathUtils.unfold(filteredModel.toExpr(), 0);
                solver.track(PathUtils.unfold(filteredModel.toExpr(), 0));
                getConjuncts(monolithicExpr.getTransExpr())
                    .forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                proofObligation
                    .getExpressions()
                    .forEach(
                        ex ->
                            solver.track(
                                PathUtils.unfold(
                                    ex, monolithicExpr.getTransOffsetIndex())));
                if (solver.check().isSat()) {
                    filteredModel.remove(var);
                } else {
                    filteredModel.put(var, origValue);
                }
            }
        }
        return filteredModel;
    }

    private Set<Expr<BoolType>> removeRedundantExpressionsUsingUnsatCore(Set<Expr<BoolType>> expressions, Collection<Expr<BoolType>> unSatCore){
        final Set<Expr<BoolType>> minimalExpressions = new HashSet<>();
        minimalExpressions.addAll(expressions);
        for (Expr<BoolType> expr : expressions) {
            if (!unSatCore.contains(
                PathUtils.unfold(expr, monolithicExpr.getTransOffsetIndex()))) {
                minimalExpressions.remove(expr);
                final boolean isSat;
                try (var wpp = new WithPushPop(solver)) {
                    for (Expr<BoolType> solverExpr : minimalExpressions) {
                        solver.track(PathUtils.unfold(solverExpr, 0));
                    }
                    solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
                    isSat = solver.check().isSat();
                }
                if (isSat) {
                    minimalExpressions.add(expr);
                }
            }
        }
        return minimalExpressions;
    }


    LinkedList<ProofObligation> tryBlock(ProofObligation mainProofObligation) {
        final LinkedList<ProofObligation> proofObligationsQueue = new LinkedList<>();
        proofObligationsQueue.add(mainProofObligation);
        while (!proofObligationsQueue.isEmpty()) {
            final ProofObligation proofObligation = proofObligationsQueue.getLast();

            if (proofObligation.getTime() == 0) {
                return proofObligationsQueue;
            }

            final SolverStatus solverStatus;
            final Collection<Expr<BoolType>> unSatCore;
            final Valuation model;
            try (var wpp = new WithPushPop(solver)) {

                frames.get(proofObligation.getTime() - 1).addFrameToSolver(VarIndexingFactory.indexing(0));

                if (optimizations.isNotBOpt()) {
                    solver.track(PathUtils.unfold(Not(And(proofObligation.getExpressions())), 0));
                }

                /*
                if (proofObligation.getTime() > 2 && optimizations.isFormerFramesopt()) {
                    frames.get(proofObligation.getTime() - 2).addNegatedFrameToSolver(VarIndexingFactory.indexing(0));
                }*/

                getConjuncts(monolithicExpr.getTransExpr())
                    .forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                proofObligation
                    .getExpressions()
                    .forEach(
                        ex ->
                            solver.track(
                                PathUtils.unfold(
                                    ex, monolithicExpr.getTransOffsetIndex())));
                solverStatus = solver.check();
                if (solverStatus.isSat()) {
                    model = solver.getModel();
                    unSatCore = null;
                } else {
                    model = null;
                    unSatCore = solver.getUnsatCore();
                }
            }
            if (solverStatus.isSat()) {
                final MutableValuation filteredModel;
                if (optimizations.isFilterOpt()) {
                    filteredModel = removeRedundantVariables(model, proofObligation);
                }else {
                    filteredModel = MutableValuation.copyOf(model);
                }
                final Collection<Expr<BoolType>> reachableExprInFormerFrame = getConjuncts(PathUtils.foldin(PathUtils.extractValuation(filteredModel, 0).toExpr(), 0));
                proofObligationsQueue.add(new ProofObligation(new HashSet<>(reachableExprInFormerFrame), proofObligation.getTime() - 1));
            }else{
                Set<Expr<BoolType>> blockedExpression = proofObligation.getExpressions();
                if (optimizations.isUnSatOpt()) {
                    blockedExpression = removeRedundantExpressionsUsingUnsatCore(blockedExpression, unSatCore);
                }

                if(optimizations.isGeneralizeOpt()) {
                    blockedExpression = generalizeIter(blockedExpression,proofObligation.getTime());
                }
                for (int i = 1; i <= proofObligation.getTime(); ++i) {
                    frames.get(i).refine(Cube.of(blockedExpression));
                }
                proofObligationsQueue.removeLast();
            }
        }
        return null;
    }

    private Set<Expr<BoolType>> generalizeIter(Set<Expr<BoolType>> blockedExpression, int currentFrameNumber) {
        boolean done = false;
        boolean isSat;
        final Set<Expr<BoolType>> minimalExpressions = new HashSet<>();
        Collection<Expr<BoolType>> unSatCore = null;
        minimalExpressions.addAll(blockedExpression);

        while (!done) {
            done = true;
            final var firstCopiedExpressions = new HashSet<Expr<BoolType>>();
            firstCopiedExpressions.addAll(minimalExpressions);
            for (Expr<BoolType> expr : firstCopiedExpressions) {
                minimalExpressions.remove(expr);
                if(checkIfExpressionIntersectsInit(minimalExpressions)) {
                    minimalExpressions.add(expr);
                }else{
                    try (var wpp = new WithPushPop(solver)) {
                        frames.get(currentFrameNumber - 1).addFrameToSolver(VarIndexingFactory.indexing(0));

                        for (Expr<BoolType> solverExpr : minimalExpressions) {
                            solver.track(PathUtils.unfold(solverExpr, 0));
                        }
                        getConjuncts(monolithicExpr.getTransExpr())
                            .forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                        solver.track(PathUtils.unfold(Not(And(minimalExpressions)),monolithicExpr.getTransOffsetIndex()));
                        isSat = solver.check().isSat();
                        if(!isSat) {
                            unSatCore = solver.getUnsatCore();
                        }
                    }
                    if(!isSat) {
                        removeRedundantExpressionsUsingUnsatCore(minimalExpressions, unSatCore);
                        done = false;
                    }
                }
            }
        }
        return blockedExpression;
    }

    public Trace<ExplState, ExprAction> checkFirst() {
        Trace<ExplState, ExprAction> intersection = checkIfFaultyIntersectsInit();
        if (intersection != null) return intersection;
        if (optimizations.isPropertyOpt()) {
            return checkIfFaultyReachableInOneStep();
        }
        return null;
    }

    private @Nullable Trace<ExplState, ExprAction> checkIfFaultyReachableInOneStep() {
        final Valuation model = frames.getFirst().checkIfTargetIsReachableValuation(Not(monolithicExpr.getPropExpr()));
        if (model != null) {
            return Trace.of(
                List.of(
                    ExplState.of(
                        PathUtils.extractValuation(
                            model,
                            VarIndexingFactory.indexing(0),
                            monolithicExpr.getVars())),
                    ExplState.of(
                        PathUtils.extractValuation(
                            model,
                            monolithicExpr.getTransOffsetIndex(),
                            monolithicExpr.getVars()))),
                List.of(MonolithicExprKt.action(monolithicExpr)));
        } else {
            return null;
        }


    }
    private boolean checkIfExpressionIntersectsInit(Set<Expr<BoolType>> expression){
        boolean isSat;
        try (var wpp = new WithPushPop(solver)) {
            for (Expr<BoolType> expr : expression) {
                solver.track(PathUtils.unfold(expr, 0));
            }
            solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
            isSat = solver.check().isSat();
        }
        return isSat;
    }

    private @Nullable Trace<ExplState, ExprAction> checkIfFaultyIntersectsInit() {
        Valuation model = frames.getFirst().checkIfContainsValuation(Not(monolithicExpr.getPropExpr()));
        if (model != null) {
            return Trace.of(
                List.of(
                    ExplState.of(
                        PathUtils.extractValuation(
                            model,
                            VarIndexingFactory.indexing(0),
                            monolithicExpr.getVars()))),
                List.of());
        }
        return null;
    }

    public ProofObligation checkCurrentFrameForInterSections(Expr<BoolType> target) {
        final Set<Expr<BoolType>> interSection;
        if (optimizations.isPropertyOpt()) {
            interSection = convertValuationToExpression(frames.get(currentFrameNumber).checkIfTargetIsReachableValuation(target));
        } else {
            interSection = convertValuationToExpression(frames.get(currentFrameNumber).checkIfContainsValuation(target));
        }
        if (interSection == null){
            return null;
        }
        return new ProofObligation(interSection, currentFrameNumber);
    }

    public boolean propagate() {
        frames.add(new Frame(frames.get(currentFrameNumber), solver, monolithicExpr,optimizations));
        currentFrameNumber++;
        if (optimizations.isPropagateOpt()) {
            for (int j = 1; j < currentFrameNumber; j++) {
                List<Clause> copyClauses =  new ArrayList<>(frames.get(j).getClauses());
                for (var clause : copyClauses) {
                    try (var wpp = new WithPushPop(solver)) {

                        frames.get(j).addFrameToSolver(VarIndexingFactory.indexing(0));
                        getConjuncts(monolithicExpr.getTransExpr())
                                .forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                        Cube blockedCube = clause.negate();
                        blockedCube.getLiterals()
                                .forEach(expr -> solver.track(PathUtils.unfold(expr, monolithicExpr.getTransOffsetIndex())));
                        if (solver.check().isUnsat()) {
                            if(optimizations.isUnsatPropagate()) {
                                var unsatCore = solver.getUnsatCore();
                                blockedCube = Cube.of(removeRedundantExpressionsUsingUnsatCore(blockedCube.getLiterals(), unsatCore));

                                if (blockedCube.getLiterals().size()<clause.getLiterals().size()) {
                                    for(int k = 1; k <= j; k++){
                                        frames.get(k).refine(blockedCube);
                                    }
                                }
                            }
                            frames.get(j + 1).refine(blockedCube);
                        }
                    }
                }
                if (frames.get(j + 1).equalsParent()) {
                    return true;
                }
            }
        } else if (currentFrameNumber > 1 && frames.get(currentFrameNumber - 1).equalsParent()) {
            return true;
        }
        return false;
    }

    public Trace<ExplState, ExprAction> makeTrace(
            LinkedList<ProofObligation> forwardProofObligations) {
        var abstractStates = new ArrayList<ExprState>();
        var abstractActions = new ArrayList<ExprAction>();
        while (!forwardProofObligations.isEmpty()) {
            final ProofObligation currentProofObligation = forwardProofObligations.getLast();
            forwardProofObligations.removeLast();

            if (!abstractStates.isEmpty())
                abstractActions.add(MonolithicExprKt.action(monolithicExpr));
            abstractStates.add(PredState.of(currentProofObligation.getExpressions()));
        }
        if (optimizations.isPropertyOpt()) {
            abstractActions.add(MonolithicExprKt.action(monolithicExpr));
            abstractStates.add(PredState.of(Not(monolithicExpr.getPropExpr())));
        }
        final ExprTraceChecker<ItpRefutation> checker =
                ExprTraceFwBinItpChecker.create(
                        monolithicExpr.getInitExpr(),
                        Not(monolithicExpr.getPropExpr()),
                        solverFactory.createItpSolver());
        final ExprTraceStatus<ItpRefutation> status =
                checker.check(Trace.of(abstractStates, abstractActions));
        checkArgument(status.isFeasible(), "Infeasible trace.");

        Trace<Valuation, ? extends Action> trace = status.asFeasible().getValuations();
        final List<MutableValuation> valuations =
                trace.getStates().stream()
                        .map(
                                it -> {
                                    final MutableValuation newValuation = new MutableValuation();
                                    it.toMap().entrySet().stream()
                                            .filter(
                                                    entry ->
                                                            monolithicExpr
                                                                    .getVars()
                                                                    .contains(entry.getKey()))
                                            .forEach(
                                                    entry ->
                                                            newValuation.put(
                                                                    entry.getKey(),
                                                                    entry.getValue()));
                                    return newValuation;
                                })
                        .toList();
        final List<ExplState> states = new ArrayList<>();
        final List<ExprAction> actions = new ArrayList<>();
        for (int i = 0; i < valuations.size(); ++i) {
            states.add(ExplState.of(valuations.get(i)));
            if (i > 0) {
                actions.add(MonolithicExprKt.action(monolithicExpr));
            }
        }
        return Trace.of(states, actions);
    }
}
