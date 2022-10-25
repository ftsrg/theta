package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddValuationCollector;
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

        MddNode rootNode = x.checkInNode(MddExpressionTemplate.of(expr, o -> (Decl) o, Z3SolverFactory.getInstance()::createSolver));

        var interpreter = x.getNodeInterpreter(rootNode);

        var recursiveCursor = interpreter.cursor();
        recursiveCursor.moveNext();
        recursiveCursor.moveNext();
        recursiveCursor.moveNext();

        try(var childCursor = recursiveCursor.valueCursor()){
            childCursor.moveNext();
            childCursor.moveNext();
        }

        recursiveCursor.moveNext();

        try(var childCursor2 = recursiveCursor.valueCursor()) {
            childCursor2.moveNext();
            childCursor2.moveNext();
        }

        recursiveCursor.moveNext();
        recursiveCursor.moveNext();

//        final Set<Valuation> valuations = MddValuationCollector.collect(rootNode);
//        System.out.println(valuations);

        final Graph graph = new MddNodeVisualizer(ExprNodeTest::nodeToString).visualize(rootNode);
        try {
            GraphvizWriter.getInstance().writeFile(graph, "/home/milan/programming/mdd.dot");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

    }

    private static String nodeToString(MddNode node){
        return node.isTerminal() ? "Terminal" : node.getRepresentation().toString();
    }

}
