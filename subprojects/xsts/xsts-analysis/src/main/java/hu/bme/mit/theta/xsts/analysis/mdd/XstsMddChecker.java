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
package hu.bme.mit.theta.xsts.analysis.mdd;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.collections.impl.RecursiveIntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddCex;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker.IterationStrategy;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddWitness;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.BfsProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.GeneralizedSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.LegacyRelationalProductProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OrNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.SimpleSaturationProvider;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeInitializer;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeNextStateDescriptor;
import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.xsts.XSTS;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

public class XstsMddChecker implements SafetyChecker<MddWitness, MddCex, Void> {

    private final SolverPool solverPool;
    private final XSTS xsts;

    private final Logger logger;
    private IterationStrategy iterationStrategy;

    private XstsMddChecker(XSTS xsts, SolverPool solverPool, Logger logger, IterationStrategy iterationStrategy) {
        this.xsts = xsts;
        this.solverPool = solverPool;
        this.logger = logger;
        this.iterationStrategy = iterationStrategy;
    }

    public static XstsMddChecker create(XSTS xsts, SolverPool solverPool, Logger logger) {
        return new XstsMddChecker(xsts, solverPool, logger, IterationStrategy.GSAT);
    }

    public static XstsMddChecker create(XSTS xsts, SolverPool solverPool, Logger logger, IterationStrategy iterationStrategy) {
        return new XstsMddChecker(xsts, solverPool, logger, iterationStrategy);
    }

    @Override
    public SafetyResult<MddWitness, MddCex> check(Void input) {

        final MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

        final MddVariableOrder stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        final MddVariableOrder transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        final MddVariableOrder initOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        final NonDetStmt envTran = NonDetStmt.of(xsts.getEnv().getStmts().stream().flatMap(e -> xsts.getTran().getStmts().stream().map(t -> (Stmt) SequenceStmt.of(List.of(e, t)))).toList());
        final var envTranToExprResult = StmtUtils.toExpr(envTran, VarIndexingFactory.indexing(0));
        final var initToExprResult = StmtUtils.toExpr(xsts.getInit(), VarIndexingFactory.indexing(0));

        for (var v : xsts.getVars()) {
            final var domainSize = /*v.getType() instanceof BoolType ? 2 :*/ 0;

            stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize));

            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(envTranToExprResult.getIndexing().get(v) == 0 ? 1 : envTranToExprResult.getIndexing().get(v)), domainSize));
            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize));

            // TODO if indexes are identical, inject v'=v
            initOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(initToExprResult.getIndexing().get(v) == 0 ? 1 : initToExprResult.getIndexing().get(v)), domainSize));
            initOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize));
        }

        final var stateSig = stateOrder.getDefaultSetSignature();
        final var transSig = transOrder.getDefaultSetSignature();
        final var initSig = initOrder.getDefaultSetSignature();

        final Expr<BoolType> initExpr = PathUtils.unfold(xsts.getInitFormula(), 0);
        final MddHandle initNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(initExpr, o -> (Decl) o, solverPool));

        Preconditions.checkState(initToExprResult.getExprs().size() == 1);
        final var initUnfold = PathUtils.unfold(initToExprResult.getExprs().stream().findFirst().get(), 0);
        final var initIdentityExprs = new ArrayList<Expr<BoolType>>();
        for (var v : xsts.getVars()) {
            if (initToExprResult.getIndexing().get(v) == 0)
                initIdentityExprs.add(Eq(v.getConstDecl(0).getRef(), v.getConstDecl(1).getRef()));
        }
        final var initExprWithIdentity = And(initUnfold, And(initIdentityExprs));
        final MddHandle initTranNode = initSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(initExprWithIdentity, o -> (Decl) o, solverPool));
        final AbstractNextStateDescriptor initNextState = MddNodeNextStateDescriptor.of(initTranNode);

        final var rel = new LegacyRelationalProductProvider(stateSig.getVariableOrder());
        final var initResult = rel.compute(initNode, initNextState, stateSig.getTopVariableHandle());

        logger.write(Level.INFO, "Created initial node");

        final List<AbstractNextStateDescriptor> descriptors = new ArrayList<>();
        for (Stmt stmt : new ArrayList<>(envTran.getStmts())) {
            final var stmtToExpr = StmtUtils.toExpr(stmt, VarIndexingFactory.indexing(0));
            var stmtUnfold = PathUtils.unfold(stmtToExpr.getExprs().stream().findFirst().get(), 0);

            final var identityExprs = new ArrayList<Expr<BoolType>>();
            for (var v : xsts.getVars()) {
                if (stmtToExpr.getIndexing().get(v) < envTranToExprResult.getIndexing().get(v))
                    identityExprs.add(Eq(v.getConstDecl(stmtToExpr.getIndexing().get(v)).getRef(), v.getConstDecl(envTranToExprResult.getIndexing().get(v)).getRef()));
                if (envTranToExprResult.getIndexing().get(v) == 0)
                    identityExprs.add(Eq(v.getConstDecl(0).getRef(), v.getConstDecl(1).getRef()));
            }
            if (!identityExprs.isEmpty()) stmtUnfold = And(stmtUnfold, And(identityExprs));

            MddHandle transitionNode = transSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(stmtUnfold, o -> (Decl) o, solverPool));
            descriptors.add(MddNodeNextStateDescriptor.of(transitionNode));
        }
        final AbstractNextStateDescriptor nextStates = OrNextStateDescriptor.create(descriptors);

        logger.write(Level.INFO, "Created next-state node, starting fixed point calculation");

        final MddHandle stateSpace;
        final Cache cache;
        switch (iterationStrategy) {
            case BFS -> {
                final var bfs = new BfsProvider(stateSig.getVariableOrder());
                stateSpace = bfs.compute(MddNodeInitializer.of(initResult), nextStates, stateSig.getTopVariableHandle());
                cache = bfs.getRelProdCache();
            }
            case SAT -> {
                final var sat = new SimpleSaturationProvider(stateSig.getVariableOrder());
                stateSpace = sat.compute(MddNodeInitializer.of(initResult), nextStates, stateSig.getTopVariableHandle());
                cache = sat.getSaturateCache();
            }
            case GSAT -> {
                final var gsat = new GeneralizedSaturationProvider(stateSig.getVariableOrder());
                stateSpace = gsat.compute(MddNodeInitializer.of(initResult), nextStates, stateSig.getTopVariableHandle());
                cache = gsat.getSaturateCache();

            }
            default -> throw new IllegalStateException("Unexpected value: " + iterationStrategy);
        }
        logger.write(Level.SUBSTEP, "Enumerated state-space");

        final Expr<BoolType> negatedPropExpr = PathUtils.unfold(Not(xsts.getProp()), 0);
        final MddHandle propNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(negatedPropExpr, o -> (Decl) o, solverPool));

        final MddHandle propViolating = (MddHandle) stateSpace.intersection(propNode);

        logger.write(Level.INFO, "Calculated violating states");

        final Long violatingSize = MddInterpreter.calculateNonzeroCount(propViolating);
        logger.write(Level.INFO, "States violating the property: " + violatingSize);

        final Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(stateSpace);
        logger.write(Level.DETAIL, "State space size: " + stateSpaceSize);

        logger.write(Level.DETAIL, "Hit count: " + cache.getHitCount());
        logger.write(Level.DETAIL, "Query count: " + cache.getQueryCount());
        logger.write(Level.DETAIL, "Cache size: " + cache.getCacheSize());

        final SafetyResult<MddWitness, MddCex> result;
        if (violatingSize != 0) {
            result = SafetyResult.unsafe(MddCex.of(propViolating), MddWitness.of(stateSpace));
        } else {
            result = SafetyResult.safe(MddWitness.of(stateSpace));
        }
        logger.write(Level.RESULT, "%s%n", result);
        return result;

    }
}
