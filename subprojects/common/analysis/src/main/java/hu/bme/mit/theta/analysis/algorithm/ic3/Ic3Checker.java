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
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.*;

public class Ic3Checker extends HardwareChecker<IC3Optimizations> {

    public Ic3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory, Logger logger) {
        this(monolithicExpr, solverFactory, new IC3Optimizations(true,true,true,true, true,true,true), logger);
    }

    public Ic3Checker(
        MonolithicExpr monolithicExpr,
        SolverFactory solverFactory, IC3Optimizations optimizations,
        Logger logger) {
        super(monolithicExpr, solverFactory, optimizations, logger);
        frames.add(new Frame(null, solver, monolithicExpr, optimizations));
    }

    @Override
    public SafetyResult<EmptyProof, Trace<ExplState, ExprAction>> check(UnitPrec prec) {
        // check if init violates prop
        var proofObligations = checkFirst();
        if (proofObligations != null) {
            var trace = makeTrace(proofObligations);
            return SafetyResult.unsafe(trace, EmptyProof.getInstance());
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
                if (propagateForward()) {
                    return SafetyResult.safe(EmptyProof.getInstance());
                }
            }
        }
    }

    protected LinkedList<ProofObligation> checkFirst() {
        var proofObligationsQueue = checkIfFaultyIntersectsInit();
        if (proofObligationsQueue != null) return proofObligationsQueue;
        if (optimizations.isPropertyOpt()) {
            return checkIfFaultyReachableInOneStep();
        }
        return null;
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
                    solver.track(PathUtils.unfold(proofObligation.getCube().negate().toExpr(), 0));
                }

                getConjuncts(monolithicExpr.getTransExpr())
                    .forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                proofObligation
                    .getCube()
                    .getLiterals()
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
                    filteredModel = removeRedundantVariablesFromProofObligation(model, proofObligation.getCube());
                }else {
                    filteredModel = MutableValuation.copyOf(model);
                }
                final Collection<Expr<BoolType>> reachableExprInFormerFrame = getConjuncts(PathUtils.foldin(PathUtils.extractValuation(filteredModel, 0).toExpr(), 0));
                proofObligationsQueue.add(new ProofObligation(Cube.of(reachableExprInFormerFrame), proofObligation.getTime() - 1));
            }else{
                Cube blockedCube = proofObligation.getCube();
                if (optimizations.isUnSatOpt()) {
                    blockedCube = removeRedundantExpressionsUsingUnsatCore(blockedCube, unSatCore, false);
                }

                if(optimizations.isGeneralizeOpt()) {
                    blockedCube = generalizeIter(blockedCube, proofObligation.getTime(), false);
                }
                for (int i = 1; i <= proofObligation.getTime(); ++i) {
                    frames.get(i).refine(blockedCube);
                }
                proofObligationsQueue.removeLast();
            }
        }
        return null;
    }

    public Trace<ExplState, ExprAction> makeTrace(
            LinkedList<ProofObligation> proofObligations) {
        var abstractStates = new ArrayList<ExprState>();
        var abstractActions = new ArrayList<ExprAction>();
        while (!proofObligations.isEmpty()) {
            final ProofObligation currentProofObligation = proofObligations.getLast();
            proofObligations.removeLast();

            if (!abstractStates.isEmpty())
                abstractActions.add(MonolithicExprKt.action(monolithicExpr));
            abstractStates.add(PredState.of(currentProofObligation.getCube().getLiterals()));
        }
        if (optimizations.isPropertyOpt()) { //this can fail, if error and init intersect
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
