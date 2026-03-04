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
package hu.bme.mit.theta.analysis.algorithm.car;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.Checker;
import hu.bme.mit.theta.analysis.algorithm.EmptyProof;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExprKt;
import hu.bme.mit.theta.analysis.algorithm.ic3.Ic3Checker;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;

public class CarCegarChecker<S extends ExprState, A extends ExprAction>
    implements SafetyChecker<EmptyProof, Trace<ExplState, ExprAction>, UnitPrec> {
  private MonolithicExpr monolithicExpr;
  private final List<OverFrame> forwardOverFrames;
  private final List<UnderFrame> backwardUnderFrames;
  private final SolverFactory solverFactory;
  private final UCSolver solver;
  private final boolean formerFramesOpt;
  private final boolean unSatOpt;
  private final boolean notBOpt;
  private final boolean propagateOpt;
  private final boolean filterOpt;

  private final boolean coverOpt;
  private int currentFrameNumber;
  private final boolean forwardTrace;
  private final boolean propertyOpt;
  private final Logger logger;

  public CarCegarChecker(
      MonolithicExpr monolithicExpr,
      boolean forwardTrace,
      SolverFactory solverFactory,
      Function<Valuation, S> valToState,
      BiFunction<Valuation, Valuation, A> biValToAction,
      Logger logger) {
    this(
        monolithicExpr,
        forwardTrace,
        solverFactory,
        true,
        true,
        true,
        true,
        true,
        true,
        true,
        logger);
  }

  public CarCegarChecker(
      MonolithicExpr monolithicExpr,
      boolean forwardTrace,
      SolverFactory solverFactory,
      boolean formerFramesOpt,
      boolean unSatOpt,
      boolean notBOpt,
      boolean propagateOpt,
      boolean filterOpt,
      boolean propertyOpt,
      boolean coverOpt,
      Logger logger) {
    this.monolithicExpr = monolithicExpr;
    this.formerFramesOpt = formerFramesOpt;
    this.unSatOpt = unSatOpt;
    this.notBOpt = notBOpt;
    this.propagateOpt = propagateOpt;
    this.filterOpt = filterOpt;
    this.forwardTrace = forwardTrace;
    this.propertyOpt = propertyOpt;
    this.coverOpt = coverOpt;
    this.logger = logger;
    this.solverFactory = solverFactory;
    forwardOverFrames = new ArrayList<>();
    backwardUnderFrames = new ArrayList<>();
    solver = solverFactory.createUCSolver();
    forwardOverFrames.add(new OverFrame(null, solver, monolithicExpr));
    forwardOverFrames.get(0).refine(monolithicExpr.getInitExpr());
    backwardUnderFrames.add(new UnderFrame(solver));
    backwardUnderFrames.get(0).expand(Not(monolithicExpr.getPropExpr()),0);
    currentFrameNumber = 0;
  }

  @Override
  public SafetyResult<EmptyProof, Trace<ExplState, ExprAction>> check(UnitPrec prec) {
    /*
    var predPrec = PredPrec.of(monolithicExpr.getInitExpr()); // todo use unitprec
    predPrec = predPrec.join(PredPrec.of(monolithicExpr.getPropExpr()));
    final Function<MonolithicExpr, PredPrec> initprec = monolithicExpr ->
        PredPrec.of(Arrays.asList(
            monolithicExpr.getPropExpr(),
            monolithicExpr.getInitExpr()
        ));*/

    final ExprTraceChecker<ItpRefutation> exprTraceFwBinItpChecker =
        ExprTraceFwBinItpChecker.create(
            monolithicExpr.getInitExpr(),
            Not(monolithicExpr.getPropExpr()),
            solverFactory.createItpSolver());
    AbstractHelper helper = new AbstractHelper(monolithicExpr -> exprTraceFwBinItpChecker);

    MonolithicExpr abstractModel = helper.createPrec(monolithicExpr);
    var checker =
        new CarChecker<>(
            abstractModel,
            true,
            Z3LegacySolverFactory.getInstance(), //todo use solverfactory
            formerFramesOpt,
            unSatOpt,
            notBOpt,
            propagateOpt,
            filterOpt,
            propertyOpt,
            coverOpt,
            logger);
    while(true){
      logger.write(Logger.Level.SUBSTEP, "Current prec: %s\n", helper.currentPrec);

      //final var abstractMonolithicExpr = AbstractMonolithicExprKt.createAbstract(monolithicExpr, predPrec);
      //checker.setMonolithicExpr(abstractMonolithicExpr);
      var result = checker.check();
      if (result.isSafe()) {
        logger.write(Logger.Level.MAINSTEP, "Model is safe, stopping CEGAR");
        return SafetyResult.safe(result.getProof());
      }else{
        Preconditions.checkState(result.isUnsafe());

        final Trace<? extends ExprState, ? extends ExprAction> cex =
            result.asUnsafe().getCex();
        Trace trace;
        if(checker.getValuations().size()>0){
          List<PredState> states = new ArrayList<>();
          for (var v : checker.getValuations()) {
            states.add(helper.activationLiteralsToPredicates(v));
          }

          var actions = cex.getActions();

          trace = Trace.of(states, actions);
        }else{
          trace = cex;
        }

        /*final ExprTraceChecker<ItpRefutation> exprTraceFwBinItpChecker =
            ExprTraceFwBinItpChecker.create(
                monolithicExpr.getInitExpr(),
                Not(monolithicExpr.getPropExpr()),
                solverFactory.createItpSolver());*/
        if (trace != null) {
          logger.write(Logger.Level.VERBOSE, "\tFound trace: %s\n", trace);
          final ExprTraceStatus<ItpRefutation> concretizationResult =
              exprTraceFwBinItpChecker.check(trace);
          if (concretizationResult.isFeasible()) {
            logger.write(Logger.Level.MAINSTEP, "Model is unsafe, stopping CEGAR\n");
            return result;
          } else {
            final var ref = concretizationResult.asInfeasible().getRefutation();
            final var newPred = ref.get(ref.getPruneIndex());
            checker.prune(ref.getPruneIndex(), false);
            final var newPrec = PredPrec.of(newPred);
            helper.currentPrec = helper.currentPrec.join(newPrec);
            logger.write(Logger.Level.INFO, "Added new predicate " + newPrec + "\n");
            final var abstractMonolithicExpr = helper.createAbstract(monolithicExpr, helper.currentPrec);
            checker.setMonolithicExpr(abstractMonolithicExpr);
          }
        }
      }
    }

  }



}
