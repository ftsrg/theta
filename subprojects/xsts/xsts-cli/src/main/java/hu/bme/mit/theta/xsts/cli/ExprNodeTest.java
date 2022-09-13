package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.ValuationCollector;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeImpl;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeTraverser;
import hu.bme.mit.theta.analysis.utils.MddSymbolicNodeVisualizer;
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

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class ExprNodeTest {

    public static void main(String[] args){

        MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        ConstDecl<IntType> declX = Decls.Const("x", Int());
        ConstDecl<IntType> declY = Decls.Const("y", Int());
        ConstDecl<IntType> declZ = Decls.Const("z", Int());

        MddVariable z = varOrder.createOnTop(MddVariableDescriptor.create(declZ, 0));
        MddVariable y = varOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));

        // x >= 2 && y = x + 1 && x <= 6
        Expr<BoolType> expr = And(Geq(declX.getRef(),Int(2)), Eq(declY.getRef(),Add(declX.getRef(),Int(1))),Leq(declX.getRef(), Int(6)));
//        Expr<BoolType> expr = Or(And(Geq(declX.getRef(),Int(2)), Eq(declY.getRef(),Int(1)),Leq(declX.getRef(), Int(6))),And(Geq(declY.getRef(), Int(5)),Gt(declX.getRef(), Int(3)), IntExprs.Lt(declX.getRef(), Int(6))));

        MddSymbolicNodeImpl rootNode = new MddSymbolicNodeImpl(new Pair<>(expr, x));

        MddSymbolicNodeTraverser traverser = ExprVariable.getNodeTraverser(rootNode);

        while (!rootNode.isComplete()) traverser.queryEdge();

        var interpreter = ExprVariable.getNodeInterpreter(rootNode, x, Z3SolverFactory.getInstance()::createSolver);

        final Set<Valuation> valuations = ValuationCollector.collect(rootNode, ExprVariable.getNodeTraverser(rootNode, Z3SolverFactory.getInstance()::createSolver));
        System.out.println(valuations);

        final Graph graph = new MddSymbolicNodeVisualizer(ExprNodeTest::nodeToString).visualize(rootNode);
        try {
            GraphvizWriter.getInstance().writeFile(graph, "/home/milan/programming/mdd.dot");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

    }

    private static String nodeToString(MddSymbolicNodeImpl node){
        final var symbolicRepresentation = node.getSymbolicRepresentation(Expr.class);
        return symbolicRepresentation.first.toString() + (symbolicRepresentation.second == null?"":", "+symbolicRepresentation.second.getTraceInfo(Decl.class).getName());
    }

}
