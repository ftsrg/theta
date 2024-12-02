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

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

import com.google.common.collect.Lists;
import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeInitializer;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.BfsProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.GeneralizedSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.SimpleSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.StateSpaceEnumerationProvider;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverPool;
import java.util.ArrayList;
import java.util.List;

public class MddChecker<A extends ExprAction> implements SafetyChecker<MddProof, MddCex, Void> {

    private final Expr<BoolType> initRel;
    private final VarIndexing initIndexing;
    private final A transRel;
    private final Expr<BoolType> safetyProperty;
    private final List<VarDecl<?>> variableOrdering;
    private final SolverPool solverPool;
    private final Logger logger;
    private IterationStrategy iterationStrategy = IterationStrategy.GSAT;

    public enum IterationStrategy {
        BFS,
        SAT,
        GSAT
    }

    private MddChecker(
            Expr<BoolType> initRel,
            VarIndexing initIndexing,
            A transRel,
            Expr<BoolType> safetyProperty,
            List<VarDecl<?>> variableOrdering,
            SolverPool solverPool,
            Logger logger,
            IterationStrategy iterationStrategy) {
        this.initRel = initRel;
        this.initIndexing = initIndexing;
        this.transRel = transRel;
        this.variableOrdering = variableOrdering;
        this.safetyProperty = safetyProperty;
        this.solverPool = solverPool;
        this.logger = logger;
        this.iterationStrategy = iterationStrategy;
    }

    public static <A extends ExprAction> MddChecker<A> create(
            Expr<BoolType> initRel,
            VarIndexing initIndexing,
            A transRel,
            Expr<BoolType> safetyProperty,
            List<VarDecl<?>> variableOrdering,
            SolverPool solverPool,
            Logger logger) {
        return new MddChecker<A>(
                initRel,
                initIndexing,
                transRel,
                safetyProperty,
                variableOrdering,
                solverPool,
                logger,
                IterationStrategy.GSAT);
    }

    public static <A extends ExprAction> MddChecker<A> create(
            Expr<BoolType> initRel,
            VarIndexing initIndexing,
            A transRel,
            Expr<BoolType> safetyProperty,
            List<VarDecl<?>> variableOrdering,
            SolverPool solverPool,
            Logger logger,
            IterationStrategy iterationStrategy) {
        return new MddChecker<A>(
                initRel,
                initIndexing,
                transRel,
                safetyProperty,
                variableOrdering,
                solverPool,
                logger,
                iterationStrategy);
    }

    @Override
    public SafetyResult<MddProof, MddCex> check(Void input) {

        final MddGraph<Expr> mddGraph =
                JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

        final MddVariableOrder stateOrder =
                JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        final MddVariableOrder transOrder =
                JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        checkArgument(
                variableOrdering.size() == Containers.createSet(variableOrdering).size(),
                "Variable ordering contains duplicates");
        final var identityExprs = new ArrayList<Expr<BoolType>>();
        for (var v : Lists.reverse(variableOrdering)) {
            var domainSize = Math.max(v.getType().getDomainSize().getFiniteSize().intValue(), 0);

            if (domainSize > 100) {
                domainSize = 0;
            }

            stateOrder.createOnTop(
                    MddVariableDescriptor.create(v.getConstDecl(initIndexing.get(v)), domainSize));

            final var index = transRel.nextIndexing().get(v);
            if (index > 0) {
                transOrder.createOnTop(
                        MddVariableDescriptor.create(
                                v.getConstDecl(transRel.nextIndexing().get(v)), domainSize));
            } else {
                transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(1), domainSize));
                identityExprs.add(Eq(v.getConstDecl(0).getRef(), v.getConstDecl(1).getRef()));
            }

            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize));
        }

        final var stateSig = stateOrder.getDefaultSetSignature();
        final var transSig = transOrder.getDefaultSetSignature();

        final Expr<BoolType> initExpr = PathUtils.unfold(initRel, initIndexing);
        final MddHandle initNode =
                stateSig.getTopVariableHandle()
                        .checkInNode(MddExpressionTemplate.of(initExpr, o -> (Decl) o, solverPool));

        logger.write(Level.INFO, "Created initial node\n");

        final Expr<BoolType> transExpr =
                And(
                        PathUtils.unfold(transRel.toExpr(), VarIndexingFactory.indexing(0)),
                        And(identityExprs));
        final MddHandle transitionNode =
                transSig.getTopVariableHandle()
                        .checkInNode(
                                MddExpressionTemplate.of(transExpr, o -> (Decl) o, solverPool));
        final AbstractNextStateDescriptor nextStates =
                MddNodeNextStateDescriptor.of(transitionNode);

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
        final MddHandle stateSpace =
                stateSpaceProvider.compute(
                        MddNodeInitializer.of(initNode),
                        nextStates,
                        stateSig.getTopVariableHandle());

        logger.write(Level.INFO, "Enumerated state-space");

        final Expr<BoolType> negatedPropExpr = PathUtils.unfold(Not(safetyProperty), initIndexing);
        final MddHandle propNode =
                stateSig.getTopVariableHandle()
                        .checkInNode(
                                MddExpressionTemplate.of(
                                        negatedPropExpr, o -> (Decl) o, solverPool));

        final MddHandle propViolating = (MddHandle) stateSpace.intersection(propNode);

        logger.write(Level.INFO, "Calculated violating states");

        final Long violatingSize = MddInterpreter.calculateNonzeroCount(propViolating);
        logger.write(Level.INFO, "States violating the property: " + violatingSize);

        final Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(stateSpace);
        logger.write(Level.DETAIL, "State space size: " + stateSpaceSize);

        final MddAnalysisStatistics statistics =
                new MddAnalysisStatistics(
                        violatingSize,
                        stateSpaceSize,
                        stateSpaceProvider.getHitCount(),
                        stateSpaceProvider.getQueryCount(),
                        stateSpaceProvider.getCacheSize());

        logger.write(Level.MAINSTEP, "%s\n", statistics);

        final SafetyResult<MddProof, MddCex> result;
        if (violatingSize != 0) {
            result =
                    SafetyResult.unsafe(
                            MddCex.of(propViolating), MddProof.of(stateSpace), statistics);
        } else {
            result = SafetyResult.safe(MddProof.of(stateSpace), statistics);
        }
        logger.write(Level.RESULT, "%s\n", result);
        return result;
    }
}
