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
//package hu.bme.mit.theta.xsts.cli;
//
//import hu.bme.mit.delta.Pair;
//import hu.bme.mit.delta.java.mdd.JavaMddFactory;
//import hu.bme.mit.delta.java.mdd.MddGraph;
//import hu.bme.mit.delta.java.mdd.MddVariable;
//import hu.bme.mit.delta.java.mdd.MddVariableOrder;
//import hu.bme.mit.delta.mdd.MddVariableDescriptor;
//import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
//import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
//import hu.bme.mit.theta.common.visualization.Graph;
//import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
//import hu.bme.mit.theta.core.decl.ConstDecl;
//import hu.bme.mit.theta.core.decl.Decl;
//import hu.bme.mit.theta.core.decl.Decls;
//import hu.bme.mit.theta.core.type.Expr;
//import hu.bme.mit.theta.core.type.booltype.BoolType;
//import hu.bme.mit.theta.core.type.inttype.IntType;
//
//import java.io.FileNotFoundException;
//
//import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
//import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
//import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
//import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
//
//public class ExprNodeTest3 {
//
//    public static void main(String[] args){
//
//        MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
//        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
//
//        ConstDecl<IntType> declX = Decls.Const("x", Int());
//        ConstDecl<IntType> declX_prime = Decls.Const("x_prime", Int());
//        ConstDecl<IntType> declY = Decls.Const("y", Int());
//        ConstDecl<IntType> declY_prime = Decls.Const("y_prime", Int());
//
//        MddVariable y_prime = varOrder.createOnTop(MddVariableDescriptor.create(declY_prime, 0));
//        MddVariable y = varOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
//        MddVariable x_prime = varOrder.createOnTop(MddVariableDescriptor.create(declX_prime, 0));
//        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));
//
//        Expr<BoolType> state = And(Eq(declX.getRef(), Int(2)), Eq(declY.getRef(), Int(0)));
//        Expr<BoolType> action = And(Eq(declX_prime.getRef(), Add(declX.getRef(), Int(1))),Eq(declY_prime.getRef(), declY.getRef()));
//
//        MddSymbolicNode stateRoot = new MddSymbolicNode(new Pair<>(state, x));
//        MddSymbolicNode actionRoot = new MddSymbolicNode(new Pair<>(action, x));
//
////        final Set<Valuation> valuations = ValuationCollector.collect(stateRoot, ExprVariable.getNodeTraverser(stateRoot, Z3SolverFactory.getInstance()::createSolver));
////        System.out.println(valuations);
////
////        final TraversalConstraint constraint = new MddSymbolicNodeTraversalConstraint(stateRoot);
////        final Set<Valuation> nextStateValuations = ValuationCollector.collect(actionRoot, ExprVariable.getConstrainedNodeTraverser(actionRoot, Z3SolverFactory.getInstance()::createSolver, constraint));
////        System.out.println(nextStateValuations);
//
//        final Graph graph = new MddNodeVisualizer(ExprNodeTest3::nodeToString).visualize(actionRoot);
//        try {
//            GraphvizWriter.getInstance().writeFile(graph, "/home/milan/programming/mdd.dot");
//        } catch (FileNotFoundException e) {
//            e.printStackTrace();
//        }
//
//    }
//
//    private static String nodeToString(MddSymbolicNode node){
//        final var symbolicRepresentation = node.getSymbolicRepresentation(Expr.class);
//        return symbolicRepresentation.first.toString() + (symbolicRepresentation.second == null?"":", "+symbolicRepresentation.second.getTraceInfo(Decl.class).getName());
//    }
//
//}