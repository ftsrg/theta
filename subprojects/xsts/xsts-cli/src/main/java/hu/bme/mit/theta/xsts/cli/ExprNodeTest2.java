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
package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddValuationCollector;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

import java.io.FileNotFoundException;
import java.util.Set;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class ExprNodeTest2 {

    public static void main(String[] args) {

        MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        ConstDecl<BoolType> declA = Decls.Const("a", Bool());
        ConstDecl<BoolType> declB = Decls.Const("b", Bool());
        ConstDecl<IntType> declX = Decls.Const("x", Int());

        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));
        MddVariable b = varOrder.createOnTop(MddVariableDescriptor.create(declB, 2));
        MddVariable a = varOrder.createOnTop(MddVariableDescriptor.create(declA, 2));

        Expr<BoolType> expr = And(Or(declA.getRef(), Not(declB.getRef())), Eq(declX.getRef(), Int(2)));

        MddNode rootNode = a.checkInNode(MddExpressionTemplate.of(expr, o -> (Decl) o, new SolverPool(Z3SolverFactory.getInstance())));

        for (var c = rootNode.cursor(); c.moveNext(); ) {
        }

        var node2 = rootNode.get(0);

        for (var c = node2.cursor(); c.moveNext(); ) {
        }

        var node3 = node2.get(0);

        for (var c = node3.cursor(); c.moveNext(); ) {
        }

        var node4 = rootNode.get(1);

        for (var c = node4.cursor(); c.moveNext(); ) {
        }

//        var node5 = node4.get(1);
//
//        for (var c = node5.cursor(); c.moveNext(); ){}


//        MddSymbolicNodeTraverser traverser = ExprVariable.getNodeTraverser(rootNode, Z3SolverFactory.getInstance()::createSolver);
//
//        while (!rootNode.isComplete()) traverser.queryEdge();
//
//        var node2 = traverser.moveDown(0);
//
//        while(!node2.isComplete()) traverser.queryEdge();
//
//        var node3 = traverser.moveDown(0);
//
//        while(!node3.isComplete()) traverser.queryEdge();
//
//        traverser.moveUp();
//        traverser.moveUp();
//
//        var node4 = traverser.moveDown(1);
//
//        while(!node4.isComplete()) traverser.queryEdge();
//
//        var node5 = traverser.moveDown(1);
//
//        while(!node5.isComplete()) traverser.queryEdge();
//
//        var interpreter = ExprVariable.getNodeInterpreter(rootNode, a, Z3SolverFactory.getInstance()::createSolver);
//
        final Set<Valuation> valuations = MddValuationCollector.collect(rootNode);
        System.out.println(valuations);

        final Graph graph = new MddNodeVisualizer(ExprNodeTest2::nodeToString).visualize(rootNode);
        try {
            GraphvizWriter.getInstance().writeFile(graph, "build\\mdd.dot");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

    }

    private static String nodeToString(MddNode node) {
        return node instanceof MddNode.Terminal ? ((MddNode.Terminal<?>) node).getTerminalData().toString() : node.getRepresentation().toString();
    }

}
