package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.expression.ExpressionNode;
import hu.bme.mit.theta.analysis.algorithm.symbolic.expression.ExpressionNodeInterpreter;
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

        ExpressionNode rootNode = new ExpressionNode(new Pair<>(expr, x),x.getLevel(),0);

        ExpressionNodeTraverser traverser = new ExpressionNodeTraverser(rootNode, Z3SolverFactory.getInstance()::createSolver);

        while(!rootNode.isComplete()) traverser.queryAssignment();

        var interpeter = ExpressionNodeInterpreter.getNodeInterpreter(rootNode, x, Z3SolverFactory.getInstance()::createSolver);

        interpeter.size();

    }

}
