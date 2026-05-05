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

package hu.bme.mit.theta.analysis.algorithm.ic3;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.EmptyProof;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExprKt;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
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
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import org.jspecify.annotations.Nullable;

import java.util.*;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;

public abstract class HardwareChecker<O extends BaseOptimizations>
    implements SafetyChecker<EmptyProof, Trace<ExplState, ExprAction>, UnitPrec> {

  protected MonolithicExpr monolithicExpr;
  protected final SolverFactory solverFactory;
  protected final UCSolver solver;
  protected final O optimizations;
  protected final Logger logger;
  protected final List<Frame> frames;
  protected int currentFrameNumber;

  protected HardwareChecker(
      MonolithicExpr monolithicExpr,
      SolverFactory solverFactory,
      O optimizations,
      Logger logger) {
    this.monolithicExpr = monolithicExpr;
    this.solverFactory = solverFactory;
    this.solver = solverFactory.createUCSolver();
    this.optimizations = optimizations;
    this.logger = logger;
    this.frames = new ArrayList<>();
    this.currentFrameNumber = 0;
  }

  protected Set<Expr<BoolType>> convertValuationToExpression(Valuation model) {
    if (model != null) {
      return new HashSet<>(getConjuncts(PathUtils.foldin(filterModel(model).toExpr(), 0)));
    } else {
      return null;
    }
  }

  protected Valuation filterModel(Valuation model) {
    return PathUtils.extractValuation(
        model,
        VarIndexingFactory.indexing(0),
        monolithicExpr.getVars());
  }

  protected Cube removeRedundantExpressionsUsingUnsatCore(Cube expressions, Collection<Expr<BoolType>> unSatCore, boolean canIntersectInit){
    final Set<Expr<BoolType>> minimalExpressions = new HashSet<>();
    minimalExpressions.addAll(expressions.getLiterals());
    for (Expr<BoolType> expr : expressions.getLiterals()) {
      if (!unSatCore.contains(
          PathUtils.unfold(expr, monolithicExpr.getTransOffsetIndex()))) {
        minimalExpressions.remove(expr);
        if(!canIntersectInit && checkIfExpressionIntersectsInit(minimalExpressions)) {
          minimalExpressions.add(expr);
        }
      }
    }
    return Cube.of(minimalExpressions);
  }

  protected boolean checkIfExpressionIntersectsInit(Set<Expr<BoolType>> expression){
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

  protected @Nullable LinkedList<ProofObligation> checkIfFaultyReachableInOneStep() {
    final Valuation model = frames.getFirst().checkIfTargetIsReachableValuation(Not(monolithicExpr.getPropExpr()));

    if (model != null) {
      var initReachableFrom = convertValuationToExpression(model);

      final LinkedList<ProofObligation> proofObligationsQueue = new LinkedList<>();

      proofObligationsQueue.add(new ProofObligation(Cube.of(initReachableFrom),0));

      return proofObligationsQueue;
    }

    return null;

  }

  protected LinkedList<ProofObligation> checkIfFaultyIntersectsInit() {
    Valuation model = frames.getFirst().checkIfContainsValuation(Not(monolithicExpr.getPropExpr()));
    if (model != null) {
      var counterExample = convertValuationToExpression(model);

      final LinkedList<ProofObligation> proofObligationsQueue = new LinkedList<>();
      proofObligationsQueue.add(new ProofObligation(Cube.of(counterExample),0));
      return proofObligationsQueue;
    }
    return null;
  }

  protected ProofObligation checkCurrentFrameForInterSections(Expr<BoolType> target) {
    final Set<Expr<BoolType>> interSection;
    if (optimizations.isPropertyOpt()) {
      interSection = convertValuationToExpression(frames.get(currentFrameNumber).checkIfTargetIsReachableValuation(target));
    } else {
      interSection = convertValuationToExpression(frames.get(currentFrameNumber).checkIfContainsValuation(target));
    }
    if (interSection == null){
      return null;
    }
    return new ProofObligation(Cube.of(interSection), currentFrameNumber);
  }

  protected boolean propagateForward() {
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
              if(optimizations.isUnsatPropagateOpt()) {
                var unsatCore = solver.getUnsatCore();
                blockedCube = removeRedundantExpressionsUsingUnsatCore(blockedCube, unsatCore, false);

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

  protected Cube generalizeIter(Cube blockedCube, int currentFrameNumber, boolean canIntersectInit) {
    boolean done = false;
    boolean isSat;
    Cube minimalCube = Cube.of(blockedCube.getLiterals());

    Collection<Expr<BoolType>> unSatCore = null;

    while (!done) {
      done = true;
      final var firstCopiedExpressions = new HashSet<Expr<BoolType>>();
      firstCopiedExpressions.addAll(minimalCube.getLiterals());
      for (Expr<BoolType> expr : firstCopiedExpressions) {
        minimalCube.removeLiteral(expr);
        if(!canIntersectInit && checkIfExpressionIntersectsInit(minimalCube.getLiterals())) {
          minimalCube.addLiteral(expr);
        }else{
          try (var wpp = new WithPushPop(solver)) {
            frames.get(currentFrameNumber - 1).addFrameToSolver(VarIndexingFactory.indexing(0));

            for (Expr<BoolType> solverExpr : minimalCube.getLiterals()) {
              solver.track(PathUtils.unfold(solverExpr, 0));
            }
            getConjuncts(monolithicExpr.getTransExpr())
                .forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
            minimalCube.negate().getLiterals().
                forEach(ex -> solver.track(PathUtils.unfold(ex, monolithicExpr.getTransOffsetIndex())));
            isSat = solver.check().isSat();
            if(!isSat) {
              unSatCore = solver.getUnsatCore();
            }
          }
          if(!isSat) {
            minimalCube =  removeRedundantExpressionsUsingUnsatCore(minimalCube, unSatCore, canIntersectInit);
            done = false;
          } else {
            minimalCube.addLiteral(expr);
          }
        }
      }
    }
    return blockedCube;
  }

  protected MutableValuation removeRedundantVariablesFromProofObligation(Valuation model, Cube cube) {

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

      try (var wpp2 = new WithPushPop(solver)) {
        solver.track(PathUtils.unfold(filteredModel.toExpr(), 0));
        getConjuncts(monolithicExpr.getTransExpr())
            .forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
        cube.getLiterals()
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



}
