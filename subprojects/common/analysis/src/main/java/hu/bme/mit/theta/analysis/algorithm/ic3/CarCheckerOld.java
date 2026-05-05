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
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;

public class CarCheckerOld<S extends ExprState, A extends ExprAction>
    extends HardwareChecker<CarOptimizations> {
  public void setMonolithicExpr(MonolithicExpr monolithicExpr) {
    this.monolithicExpr = monolithicExpr;
  }


  private final boolean curFrameopt = false;

  private final Map<Node, Boolean> currentlyVisited;

  private Node root;

  private Node errorNode;

  private int errorLength;

  private int pruneLength;

  public List<MutableValuation> getValuations() {
    return valuations;
  }

  private List<MutableValuation> valuations;

  private boolean pruneOpt = true;

  public CarCheckerOld(
      MonolithicExpr monolithicExpr,
      SolverFactory solverFactory,
      Logger logger) {
    this(
        monolithicExpr,
        solverFactory,
        new CarOptimizations(
            true,
            true,
            true,
            true,
            true,
            true,
            true,
            true),
        logger);
  }

  public CarCheckerOld(
      MonolithicExpr monolithicExpr,
      SolverFactory solverFactory,
      CarOptimizations optimizations,
      Logger logger) {

    super(monolithicExpr, solverFactory, optimizations, logger);

    frames.add(new Frame(null, solver, monolithicExpr, optimizations));
    valuations = new ArrayList<>();
    root = new Node(Not(monolithicExpr.getPropExpr()),null, optimizations.isCoverOpt(), solver);
    currentlyVisited = Containers.createMap();

  }

  private Node getNotCheckedNode(){
    if(currentlyVisited.size()==0){
      root = new Node(Not(monolithicExpr.getPropExpr()),null, optimizations.isCoverOpt(), solver);
      currentlyVisited.put(root,false);
    }
    for(Node node : currentlyVisited.keySet()){ //todo can be more faster if the nodes visited in a more specific order
      if(!currentlyVisited.get(node)){

        return node;
      }
    }
    return null;
  }

  @Override
  public SafetyResult<EmptyProof, Trace<ExplState, ExprAction>> check(UnitPrec prec) {
    if(!curFrameopt) {
      currentFrameNumber = 0;
    }
    noNodeIsVisited();
    pruneLength = 0;

    root.setExprs(Not(monolithicExpr.getPropExpr()));

    var faultyNodeInit = checkFirstCar();
    if (faultyNodeInit != null) {
      var trace = makeTrace(faultyNodeInit);
      final var result = SafetyResult.unsafe(trace, EmptyProof.getInstance());
      logger.writeln(Logger.Level.RESULT, result.toString());
      return result;
    }
    while (true) {
      while(true){
        Node node = getNotCheckedNode();
        if(node == null){
          break;
        }
        /*
        Node counterExampleNode;
        var counterExampleProof = checkCurrentFrameForInterSections(And(node.getExprs()));
        if (counterExampleProof == null) {
          counterExampleNode = null;
        } else {
          counterExampleNode = new Node(counterExampleProof.getCube().toExpr(), node, optimizations.isCoverOpt(),solver);
          currentlyVisited.put(counterExampleNode,false);
        }*/
        Node counterExampleNode = checkCurrentFrame(node);
        if (counterExampleNode != null) {
          var faultyNode =
              tryBlock(new ProofObligationCar(counterExampleNode, currentFrameNumber));
          if (faultyNode != null) {
            var trace = makeTrace(faultyNode);
            if(trace != null){
              final var result = SafetyResult.unsafe(trace, EmptyProof.getInstance());
              logger.writeln(Logger.Level.RESULT, result.toString());
              return result;
            }
          }
        }else{
          currentlyVisited.put(node,true);
        }
      }
      if (propagate()) {
        final SafetyResult<EmptyProof, Trace<ExplState, ExprAction>> result =
            SafetyResult.safe(EmptyProof.getInstance());
        logger.writeln(Logger.Level.RESULT, result.toString());
        return result;
      }

    }
  }
  private void delete(Node node){
    //todo use childlist for this
    var deleteList = new ArrayList<Node>();
    for(Node currentNode : currentlyVisited.keySet()){
      if(currentNode.getParent() != null && currentNode.getParent().equals(node)){
        deleteList.add(currentNode);
      }
    }
    for(var currentNode : deleteList){
      delete(currentNode);
    }
    currentlyVisited.remove(node);
  }
  public void prune(int pruneIndex, boolean more){
    while((errorLength > pruneIndex + 1) && !errorNode.equals(root)){
      errorLength--;
      Node previousNode = errorNode;
      delete(previousNode);
      errorNode = errorNode.getParent();
    }
  }

  Node tryBlock(ProofObligationCar mainProofObligation) {
    final LinkedList<ProofObligationCar> proofObligationsQueue = new LinkedList<ProofObligationCar>();
    proofObligationsQueue.add(mainProofObligation);
    while (!proofObligationsQueue.isEmpty()) {
      final ProofObligationCar proofObligation = proofObligationsQueue.getLast();

      if (proofObligation.getTime() == 0) {
        return proofObligation.getNode();
      }

      final Collection<Expr<BoolType>> b;
      final Collection<Expr<BoolType>> unSatCore;
      try (var wpp = new WithPushPop(solver)) {
        frames.get(proofObligation.getTime() - 1).addFrameToSolver(VarIndexingFactory.indexing(0));
        if (optimizations.isNotBOpt()) {
          solver.track(PathUtils.unfold(Not(And(proofObligation.getNode().getExprs())), 0));
        }
        /*
        if (proofObligation.getTime() > 2 && formerFramesOpt) { // lehet, hogy 1, vagy 2??
          solver.track(
              PathUtils.unfold(
                  Not(And(forwardOverFrames.get(proofObligation.getTime() - 2).getExprs())),
                  monolithicExpr
                      .getTransOffsetIndex())); // 2 vel korábbi frame-ban
          // levő dolgok
        }*/

        getConjuncts(monolithicExpr.getTransExpr())
            .forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
        proofObligation
            .getNode()
            .getExprs()
            .forEach(
                ex ->
                    solver.track(
                        PathUtils.unfold(
                            ex, monolithicExpr.getTransOffsetIndex())));

        if (solver.check().isSat()) {
          final Valuation model = solver.getModel();

          final MutableValuation filteredModel = new MutableValuation();
          monolithicExpr.getVars().stream()
              .map(varDecl -> varDecl.getConstDecl(0))
              .filter(model.toMap()::containsKey)
              .forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
          if (optimizations.isFilterOpt()) {
            var vars = Containers.createSet(filteredModel.toMap().keySet());
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
                if (solver.check().isSat()) {
                  filteredModel.remove(var);
                } else {
                  filteredModel.put(var, origValue);
                }
              }
            }
          }
          b =
              getConjuncts(
                  PathUtils.foldin(
                      PathUtils.extractValuation(filteredModel, 0).toExpr(),
                      0));
          unSatCore = null;
        } else {
          b = null;
          unSatCore = solver.getUnsatCore();
        }
      }
      if (b == null) {

        final Collection<Expr<BoolType>> newCore = new ArrayList<Expr<BoolType>>();
        newCore.addAll(proofObligation.getNode().getExprs());
        if (optimizations.isUnSatOpt()) {
          for (Expr<BoolType> i : proofObligation.getNode().getExprs()) {
            if (!unSatCore.contains(
                PathUtils.unfold(i, monolithicExpr.getTransOffsetIndex()))) {
              newCore.remove(i);
              final boolean isSat;
              try (var wpp = new WithPushPop(solver)) {
                for (Expr<BoolType> solverex : newCore) {
                  solver.track(PathUtils.unfold(solverex, 0));
                }
                solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
                isSat = solver.check().isSat();
              }
              if (isSat) {
                newCore.add(i);
              }
            }
          }
        }
        for (int i = 1; i <= proofObligation.getTime(); ++i) {
          frames.get(i).refine(Cube.of(newCore));
        }
        proofObligationsQueue.removeLast();
      } else {
        Node newNode = new Node(And(b),proofObligation.getNode(),optimizations.isCoverOpt(), solver);
        currentlyVisited.put(newNode,false);
        proofObligationsQueue.add(new ProofObligationCar(newNode, proofObligation.getTime() - 1));
      }
    }
    return null;
  }

  public Node checkFirstCar() {
    if (optimizations.isPropertyOpt()) {
      try (var wpp = new WithPushPop(solver)) {
        solver.track(
            PathUtils.unfold(
                monolithicExpr.getInitExpr(), VarIndexingFactory.indexing(0)));
        solver.track(
            PathUtils.unfold(
                monolithicExpr.getTransExpr(),
                VarIndexingFactory.indexing(0)));
        solver.track(
            PathUtils.unfold(
                Not(monolithicExpr.getPropExpr()),
                monolithicExpr.getTransOffsetIndex()));
        if (solver.check().isSat()) {
          final Valuation model = solver.getModel();
          final MutableValuation filteredModel = new MutableValuation();
          monolithicExpr.getVars().stream()
              .map(varDecl -> varDecl.getConstDecl(0))
              .filter(model.toMap()::containsKey)
              .forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));

          var counterExample = getConjuncts(PathUtils.foldin(filteredModel.toExpr(), 0));

          Node newNode = new Node(And(counterExample),root,optimizations.isCoverOpt(),solver);

          currentlyVisited.put(newNode,false);

          return newNode;



        } else {
          return null;
        }
      }
    } else {
      return null;
    }
  }
  public Node checkCurrentFrame(Node target) {
    if (optimizations.isPropertyOpt()) {
      var interSection = convertValuationToExpression(frames.get(currentFrameNumber).checkIfTargetIsReachableValuation(And(target.getExprs())));
      try (var wpp = new WithPushPop(solver)) {
        frames.get(currentFrameNumber).addFrameToSolver(VarIndexingFactory.indexing(0));
        getConjuncts(monolithicExpr.getTransExpr())
            .forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
        target.getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, monolithicExpr.getTransOffsetIndex())));

        if (solver.check().isSat()) {
          final Valuation model = solver.getModel();
          final MutableValuation filteredModel = new MutableValuation();
          monolithicExpr.getVars().stream()
              .map(varDecl -> varDecl.getConstDecl(0))
              .filter(model.toMap()::containsKey)
              .forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));

          var counterExample = getConjuncts(PathUtils.foldin(filteredModel.toExpr(), 0));

          Node newNode = new Node(And(counterExample),target,optimizations.isCoverOpt(),solver);

          currentlyVisited.put(newNode,false);

          return newNode;

        }
      }

      return null;


    } else {
      var counterExample = convertValuationToExpression(frames.get(currentFrameNumber).checkIfContainsValuation(And(target.getExprs())));
      if(counterExample == null){
        return null; //no intersection found
      }else{
        Node newNode = new Node(And(counterExample),target,optimizations.isCoverOpt(),solver);

        currentlyVisited.put(newNode,false);
        return newNode;
      }
    }
  }
  private void noNodeIsVisited(){
    for(Node node : currentlyVisited.keySet()){
      currentlyVisited.put(node,false);
    }
  }

  public boolean propagate() {
    noNodeIsVisited();
    if(frames.size()<=currentFrameNumber+1){ //todo if needed?
      frames.add(new Frame(frames.get(currentFrameNumber), solver, monolithicExpr,optimizations));
    }
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
          if(curFrameopt){
            Node node = null;
            Node counterExampleNode = null;
            do{
              node = getNotCheckedNode();
              if(node != null){
                counterExampleNode = checkCurrentFrame(node);
              }

            }while(node != null && counterExampleNode != null);
            noNodeIsVisited();
            if(counterExampleNode != null){
              logger.write(Logger.Level.SUBSTEP, "Current frame faulty: %s\n", currentFrameNumber);
              return false;
            }
          }

          return true;
        }
      }
    } else if (currentFrameNumber > 1 && frames.get(currentFrameNumber - 1).equalsParent()) {
      logger.write(Logger.Level.VERBOSE, "\tFound safety: %s\n", currentFrameNumber);
      return true;
    }
    return false;
  }

  public Trace<ExplState, ExprAction> makeTrace(Node faultyNode) {
    errorLength = 0;
    errorNode = faultyNode;
    var abstractStates = new ArrayList<ExprState>();
    var abstractActions = new ArrayList<ExprAction>();
    Node currentNode = faultyNode;
    while (currentNode != null) {
      errorLength++;

      if (!abstractStates.isEmpty())
        abstractActions.add(MonolithicExprKt.action(monolithicExpr));
      abstractStates.add(PredState.of(currentNode.getExprs()));
      currentNode = currentNode.getParent();

    }
    logger.write(Logger.Level.VERBOSE, "\tFound trace curframenumber: %s\n", currentFrameNumber);
    logger.write(Logger.Level.VERBOSE, "\tFound trace tracelength: %s\n", errorLength);

    final ExprTraceChecker<ItpRefutation> checker =
        ExprTraceFwBinItpChecker.create(
            monolithicExpr.getInitExpr(),
            Not(monolithicExpr.getPropExpr()),
            solverFactory.createItpSolver());
    ExprTraceStatus<ItpRefutation> status =
        checker.check(Trace.of(abstractStates, abstractActions));
    if(status.isInfeasible()){
      final var ref = status.asInfeasible().getRefutation();
      if(pruneOpt){
        pruneLength++;
        prune(ref.getPruneIndex()-pruneLength,true);
        noNodeIsVisited();
        return null;
      }else{
        prune(ref.getPruneIndex(),true);
        errorNode.addExpr(ref.get(ref.getPruneIndex())); //todo maybe prune children?
        noNodeIsVisited();
        return null;

      }


    }
    checkArgument(status.isFeasible(), "Infeasible trace.");

    Trace<Valuation, ? extends Action> trace = status.asFeasible().getValuations();
    valuations = new ArrayList<>();
    valuations =
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

