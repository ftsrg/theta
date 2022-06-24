package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExpressionVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNode;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeTraverser;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.MddSymbolicNodeVisualizer;
import hu.bme.mit.theta.analysis.utils.TraceVisualizer;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

import java.io.FileNotFoundException;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class ExpressionNodeTest {

    public static void main(String[] args){

        MddGraph<Boolean> mddGraph = JavaMddFactory.getDefault().createMddGraph(LatticeDefinition.forSets());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        Decl<IntType> declX = Decls.Const("x", Int());
        Decl<IntType> declY = Decls.Const("y", Int());

        MddVariable y = varOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));

        // x >= 2 && y = x + 1 && x <= 6
//        Expr<BoolType> expr = And(Geq(declX.getRef(),Int(2)), Eq(declY.getRef(),Add(declX.getRef(),Int(1))),Leq(declX.getRef(), Int(6)));
        Expr<BoolType> expr = Or(And(Geq(declX.getRef(),Int(2)), Eq(declY.getRef(),Int(1)),Leq(declX.getRef(), Int(6))),And(Geq(declY.getRef(), Int(5)),Gt(declX.getRef(), Int(3)), IntExprs.Lt(declX.getRef(), Int(6))));

        MddSymbolicNode rootNode = new MddSymbolicNode(new Pair<>(expr, x), x.getLevel(), 0);

        var incompleteInterpreter = ExpressionVariable.getNodeInterpreter(rootNode, x, Z3SolverFactory.getInstance()::createSolver);

        var node2 = incompleteInterpreter.get(4);

        MddSymbolicNodeTraverser traverser = ExpressionVariable.getNodeTraverser(rootNode, Z3SolverFactory.getInstance()::createSolver);

        while(!rootNode.isComplete()) traverser.queryChild();

        var interpreter = ExpressionVariable.getNodeInterpreter(rootNode, x, Z3SolverFactory.getInstance()::createSolver);

        final Graph graph = new MddSymbolicNodeVisualizer(ExpressionNodeTest::nodeToString).visualize(rootNode);
        try {
            GraphvizWriter.getInstance().writeFile(graph, "/home/milan/programming/mdd.dot");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

    }

    private static String nodeToString(MddSymbolicNode node){
        final var symbolicRepresentation = node.getSymbolicRepresentation(Pair.class);
        return symbolicRepresentation.first.toString() + (symbolicRepresentation.second == null?"":", "+((MddVariable)symbolicRepresentation.second).getTraceInfo(Decl.class).getName());
    }

}
