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
import hu.bme.mit.theta.analysis.algorithm.symbolic.checker.MddCex;
import hu.bme.mit.theta.analysis.algorithm.symbolic.checker.MddWitness;
import hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint.GeneralizedSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint.LegacyRelationalProductProvider;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.impl.OrNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeInitializer;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeNextStateDescriptor;
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
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

public class XstsMddChecker implements SafetyChecker<MddWitness, MddCex, Void> {

    private final SolverFactory solverFactory;
    private final XSTS xsts;

    private XstsMddChecker(XSTS xsts, SolverFactory solverFactory) {
        this.xsts = xsts;
        this.solverFactory = solverFactory;
    }

    public static XstsMddChecker create(XSTS xsts, SolverFactory solverFactory) {
        return new XstsMddChecker(xsts, solverFactory);
    }

    @Override
    public SafetyResult<MddWitness, MddCex> check(Void input) {

        try (var solverPool = new SolverPool(solverFactory)) {
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

            final var gs = new GeneralizedSaturationProvider(stateSig.getVariableOrder());
            final MddHandle satResult = gs.compute(MddNodeInitializer.of(initResult), nextStates, stateSig.getTopVariableHandle());

            final Expr<BoolType> negatedPropExpr = PathUtils.unfold(Not(xsts.getProp()), 0);
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
            final Graph stateSpaceGraph = new MddNodeVisualizer(XstsMddChecker::nodeToString).visualize(satResult.getNode());
            final Graph violatingGraph = new MddNodeVisualizer(XstsMddChecker::nodeToString).visualize(propViolating.getNode());
            try {
                GraphvizWriter.getInstance().writeFile(stateSpaceGraph, "build\\statespace.dot");
                GraphvizWriter.getInstance().writeFile(violatingGraph, "build\\violating.dot");
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }

            if (violatingSize != 0)
                return SafetyResult.unsafe(MddCex.of(propViolating), MddWitness.of(satResult));
            else return SafetyResult.safe(MddWitness.of(satResult));
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        } catch (OutOfMemoryError err) {
            err.printStackTrace();
            throw new RuntimeException(err);
        } catch (Throwable t) {
            t.printStackTrace();
            throw new RuntimeException(t);
        }


    }

    private static String nodeToString(MddNode node) {
        if (node.getRepresentation() instanceof RecursiveIntObjMapViews.OfIntObjMapView<?, ?>)
            return "";
        return node instanceof MddNode.Terminal ? ((MddNode.Terminal<?>) node).getTerminalData().toString() : node.getRepresentation().toString();
    }
}
