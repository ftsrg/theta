package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.expression.ExpressionVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.expression.MddSymbolicNode;
import hu.bme.mit.theta.analysis.algorithm.symbolic.expression.ExpressionNodeTraverser;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
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
        Expr<BoolType> expr = And(Geq(declX.getRef(),Int(2)), Eq(declY.getRef(),Add(declX.getRef(),Int(1))),Leq(declX.getRef(), Int(6)));

        MddSymbolicNode rootNode = new MddSymbolicNode(expr, x, x.getLevel(), 0);

        var incompleteInterpreter = ExpressionVariable.getNodeInterpreter(rootNode, x, Z3SolverFactory.getInstance()::createSolver);

        var node2 = incompleteInterpreter.get(2);

        ExpressionNodeTraverser traverser = new ExpressionNodeTraverser(rootNode, Z3SolverFactory.getInstance()::createSolver);

        while(!rootNode.isComplete()) traverser.queryChild();

        var interpreter = ExpressionVariable.getNodeInterpreter(rootNode, x, Z3SolverFactory.getInstance()::createSolver);

        interpreter.size();

    }

}
