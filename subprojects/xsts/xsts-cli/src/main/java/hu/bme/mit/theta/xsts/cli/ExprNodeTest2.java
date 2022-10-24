package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.utils.MddSymbolicNodeVisualizer;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.io.FileNotFoundException;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class ExprNodeTest2 {

    public static void main(String[] args){

        MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        ConstDecl<BoolType> declA = Decls.Const("a", Bool());
        ConstDecl<BoolType> declB = Decls.Const("b", Bool());
        ConstDecl<IntType> declX = Decls.Const("x", Int());

        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));
        MddVariable b = varOrder.createOnTop(MddVariableDescriptor.create(declB, 2));
        MddVariable a = varOrder.createOnTop(MddVariableDescriptor.create(declA, 2));

        Expr<BoolType> expr = And(Or(declA.getRef(),Not(declB.getRef())), Eq(declX.getRef(), Int(2)));

        MddSymbolicNode rootNode = new MddSymbolicNode(new Pair<>(expr, a));

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
//        final Set<Valuation> valuations = ValuationCollector.collect(rootNode, ExprVariable.getNodeTraverser(rootNode, Z3SolverFactory.getInstance()::createSolver));
//        System.out.println(valuations);

        final Graph graph = new MddSymbolicNodeVisualizer(ExprNodeTest2::nodeToString).visualize(rootNode);
        try {
            GraphvizWriter.getInstance().writeFile(graph, "/home/milan/programming/mdd.dot");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

    }

    private static String nodeToString(MddSymbolicNode node){
        final var symbolicRepresentation = node.getSymbolicRepresentation(Expr.class);
        return symbolicRepresentation.first.toString() + (symbolicRepresentation.second == null?"":", "+symbolicRepresentation.second.getTraceInfo(Decl.class).getName());
    }

}
