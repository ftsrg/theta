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
package hu.bme.mit.theta.analysis.algorithm.symbolic.checker;

import hu.bme.mit.delta.collections.impl.RecursiveIntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint.GeneralizedSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeInitializer;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeNextStateDescriptor;
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
    private final SolverFactory solverFactory;
    private final Logger logger;

    private MddChecker(Expr<BoolType> initRel,
                       VarIndexing initIndexing,
                       A transRel,
                       Expr<BoolType> safetyProperty,
                       SolverFactory solverFactory,
                       Logger logger) {
        this.initRel = initRel;
        this.initIndexing = initIndexing;
        this.transRel = transRel;
        this.safetyProperty = safetyProperty;
        this.solverFactory = solverFactory;
        this.logger = logger;
    }

    public static <A extends ExprAction> MddChecker<A> create(Expr<BoolType> initRel,
                                                              VarIndexing initIndexing,
                                                              A transRel,
                                                              Expr<BoolType> safetyProperty,
                                                              SolverFactory solverFactory,
                                                              Logger logger) {
        return new MddChecker<A>(initRel, initIndexing, transRel, safetyProperty, solverFactory, logger);
    }

    @Override
    public SafetyResult<MddWitness, MddCex> check(Void input) {

        try (var solverPool = new SolverPool(solverFactory)) {
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

            final Expr<BoolType> transExpr = PathUtils.unfold(transRel.toExpr(), VarIndexingFactory.indexing(0));
            final MddHandle transitionNode = transSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(transExpr, o -> (Decl) o, solverPool));
            final AbstractNextStateDescriptor nextStates = MddNodeNextStateDescriptor.of(transitionNode);

            final var gs = new GeneralizedSaturationProvider(stateSig.getVariableOrder());
            final MddHandle satResult = gs.compute(MddNodeInitializer.of(initNode), nextStates, stateSig.getTopVariableHandle());

            final Expr<BoolType> negatedPropExpr = PathUtils.unfold(Not(safetyProperty), initIndexing);
            final MddHandle propNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(negatedPropExpr, o -> (Decl) o, solverPool));

            final MddHandle propViolating = (MddHandle) satResult.intersection(propNode);

            final Long violatingSize = MddInterpreter.calculateNonzeroCount(propViolating);
            System.out.println("States violating the property: " + violatingSize);

            final Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(satResult);
            System.out.println("State space size: " + stateSpaceSize);

            System.out.println("Hit count: " + gs.getSaturateCache().getHitCount());
            System.out.println("Query count: " + gs.getSaturateCache().getQueryCount());
            System.out.println("Cache size: " + gs.getSaturateCache().getCacheSize());
//
            final Graph stateSpaceGraph = new MddNodeVisualizer(MddChecker::nodeToString).visualize(satResult.getNode());
            final Graph violatingGraph = new MddNodeVisualizer(MddChecker::nodeToString).visualize(propViolating.getNode());
//          final Graph transGraph = new MddNodeVisualizer(MddChecker::nodeToString).visualize(transitionNode.getNode());
            final Graph initGraph = new MddNodeVisualizer(MddChecker::nodeToString).visualize(initNode.getNode());
            try {
                GraphvizWriter.getInstance().writeFile(stateSpaceGraph, "build\\statespace.dot");
                GraphvizWriter.getInstance().writeFile(violatingGraph, "build\\violating.dot");
//              GraphvizWriter.getInstance().writeFile(transGraph, "build\\trans.dot");
                GraphvizWriter.getInstance().writeFile(initGraph, "build\\init.dot");
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }

            if (violatingSize != 0)
                return SafetyResult.unsafe(MddCex.of(propViolating), MddWitness.of(satResult));
            else return SafetyResult.safe(MddWitness.of(satResult));
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private static String nodeToString(MddNode node) {
        if (node.getRepresentation() instanceof RecursiveIntObjMapViews.OfIntObjMapView<?, ?>)
            return "";
        return node instanceof MddNode.Terminal ? ((MddNode.Terminal<?>) node).getTerminalData().toString() : node.getRepresentation().toString();
    }
}