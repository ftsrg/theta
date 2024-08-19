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
package hu.bme.mit.theta.analysis.algorithm.mdd;

import hu.bme.mit.delta.collections.impl.RecursiveIntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.BfsProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.GeneralizedSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.SimpleSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.StateSpaceEnumerationProvider;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeInitializer;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeNextStateDescriptor;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;

import java.io.FileNotFoundException;
import java.util.List;
import java.util.Set;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

public class MddChecker<A extends ExprAction> implements SafetyChecker<MddWitness, MddCex, Void> {

    private final Expr<BoolType> initRel;
    private final VarIndexing initIndexing;
    private final A transRel;
    private final Expr<BoolType> safetyProperty;
    private final SolverPool solverPool;
    private final Logger logger;
    private IterationStrategy iterationStrategy = IterationStrategy.GSAT;

    public enum IterationStrategy {
        BFS, SAT, GSAT
    }

    private MddChecker(Expr<BoolType> initRel,
                       VarIndexing initIndexing,
                       A transRel,
                       Expr<BoolType> safetyProperty,
                       SolverPool solverPool,
                       Logger logger,
                       IterationStrategy iterationStrategy) {
        this.initRel = initRel;
        this.initIndexing = initIndexing;
        this.transRel = transRel;
        this.safetyProperty = safetyProperty;
        this.solverPool = solverPool;
        this.logger = logger;
        this.iterationStrategy = iterationStrategy;
    }

    public static <A extends ExprAction> MddChecker<A> create(Expr<BoolType> initRel,
                                                              VarIndexing initIndexing,
                                                              A transRel,
                                                              Expr<BoolType> safetyProperty,
                                                              SolverPool solverPool,
                                                              Logger logger) {
        return new MddChecker<A>(initRel, initIndexing, transRel, safetyProperty, solverPool, logger, IterationStrategy.GSAT);
    }

    public static <A extends ExprAction> MddChecker<A> create(Expr<BoolType> initRel,
                                                              VarIndexing initIndexing,
                                                              A transRel,
                                                              Expr<BoolType> safetyProperty,
                                                              SolverPool solverPool,
                                                              Logger logger,
                                                              IterationStrategy iterationStrategy) {
        return new MddChecker<A>(initRel, initIndexing, transRel, safetyProperty, solverPool, logger, iterationStrategy);
    }

    @Override
    public SafetyResult<MddWitness, MddCex> check(Void input) {

        final MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

        final MddVariableOrder stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        final MddVariableOrder transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        final Set<VarDecl<?>> vars = ExprUtils.getVars(List.of(initRel, transRel.toExpr(), safetyProperty));
        for (var v : vars) {
            final var domainSize = v.getType() instanceof BoolType ? 2 : 0;

            stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(initIndexing.get(v)), domainSize));

            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(transRel.nextIndexing().get(v)), domainSize));
            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize));
        }

        final var stateSig = stateOrder.getDefaultSetSignature();
        final var transSig = transOrder.getDefaultSetSignature();

        final Expr<BoolType> initExpr = PathUtils.unfold(initRel, initIndexing);
        final MddHandle initNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(initExpr, o -> (Decl) o, solverPool));

        logger.write(Level.INFO, "Created initial node");

        final Expr<BoolType> transExpr = PathUtils.unfold(transRel.toExpr(), VarIndexingFactory.indexing(0));
        final MddHandle transitionNode = transSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(transExpr, o -> (Decl) o, solverPool));
        final AbstractNextStateDescriptor nextStates = MddNodeNextStateDescriptor.of(transitionNode);

        logger.write(Level.INFO, "Created next-state node, starting fixed point calculation");

        final StateSpaceEnumerationProvider stateSpaceProvider;
        switch (iterationStrategy) {
            case BFS -> {
                stateSpaceProvider = new BfsProvider(stateSig.getVariableOrder());
            }
            case SAT -> {
                stateSpaceProvider = new SimpleSaturationProvider(stateSig.getVariableOrder());
            }
            case GSAT -> {
                stateSpaceProvider = new GeneralizedSaturationProvider(stateSig.getVariableOrder());
            }
            default -> throw new IllegalStateException("Unexpected value: " + iterationStrategy);
        }
        final MddHandle stateSpace = stateSpaceProvider.compute(MddNodeInitializer.of(initNode), nextStates, stateSig.getTopVariableHandle());

        logger.write(Level.INFO, "Enumerated state-space");

        final Expr<BoolType> negatedPropExpr = PathUtils.unfold(Not(safetyProperty), initIndexing);
        final MddHandle propNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(negatedPropExpr, o -> (Decl) o, solverPool));

        final MddHandle propViolating = (MddHandle) stateSpace.intersection(propNode);

        logger.write(Level.INFO, "Calculated violating states");

        final Long violatingSize = MddInterpreter.calculateNonzeroCount(propViolating);
        logger.write(Level.INFO, "States violating the property: " + violatingSize);

        final Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(stateSpace);
        logger.write(Level.DETAIL, "State space size: " + stateSpaceSize);

        final MddAnalysisStatistics statistics = new MddAnalysisStatistics(violatingSize, stateSpaceSize, stateSpaceProvider.getHitCount(), stateSpaceProvider.getQueryCount(), stateSpaceProvider.getCacheSize());

        final SafetyResult<MddWitness, MddCex> result;
        if (violatingSize != 0) {
            result = SafetyResult.unsafe(MddCex.of(propViolating), MddWitness.of(stateSpace), statistics);
        } else {
            result = SafetyResult.safe(MddWitness.of(stateSpace), statistics);
        }
        logger.write(Level.RESULT, "%s%n", result);
        return result;
    }
}
