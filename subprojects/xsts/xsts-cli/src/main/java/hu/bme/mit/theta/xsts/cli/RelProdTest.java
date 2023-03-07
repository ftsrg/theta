package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint.RelationalProductProvider;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeNextStateDescriptor;
import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

import java.io.FileNotFoundException;
import java.util.List;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class RelProdTest {

    public static void main(String[] args){

        MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

        ConstDecl<IntType> declX = Decls.Const("x", Int());
        ConstDecl<IntType> declXPrime = Decls.Const("x_prime", Int());
        ConstDecl<IntType> declY = Decls.Const("y", Int());
        ConstDecl<IntType> declYPrime = Decls.Const("y_prime", Int());

        MddVariableOrder transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        MddVariable y_prime_trans = transOrder.createOnTop(MddVariableDescriptor.create(declYPrime, 0));
        MddVariable y_trans = transOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
        MddVariable x_prime_trans = transOrder.createOnTop(MddVariableDescriptor.create(declXPrime, 0));
        MddVariable x_trans = transOrder.createOnTop(MddVariableDescriptor.create(declX, 0));

        var transSig = transOrder.getDefaultSetSignature();
        var stateSig = (MddSignature) transOrder.createSignatureFromTraceInfos(List.of(declX, declY));

        // x = 0, y = 0
        Expr<BoolType> initExpr = And(Eq(declX.getRef(),Int(0)), Eq(declY.getRef(),Int(0)));

        MddHandle initNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(initExpr, o -> (Decl) o, Z3SolverFactory.getInstance()::createSolver));

        // x' = x + 1, y' = y - 1
        Expr<BoolType> transExpr = And(Eq(declXPrime.getRef(),Add(declX.getRef(), Int(1))), Eq(declYPrime.getRef(),Sub(declY.getRef(),Int(1))), IntExprs.Lt(declXPrime.getRef(), Int(6)));

        MddHandle transitionNode = transSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(transExpr, o -> (Decl) o, Z3SolverFactory.getInstance()::createSolver));
        AbstractNextStateDescriptor nextStates = new MddNodeNextStateDescriptor(transitionNode);

        var relprod = new RelationalProductProvider(stateSig.getVariableOrder());
        var resNode = relprod.compute(initNode, nextStates, stateSig.getTopVariableHandle());

        final Graph graph = new MddNodeVisualizer(RelProdTest::nodeToString).visualize(resNode.getNode());
        try {
            GraphvizWriter.getInstance().writeFile(graph, "/home/milan/programming/mdd.dot");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

    }

    private static String nodeToString(MddNode node){
        return node instanceof MddNode.Terminal ? ((MddNode.Terminal<?>) node).getTerminalData().toString() : node.getRepresentation().toString();
    }

}
