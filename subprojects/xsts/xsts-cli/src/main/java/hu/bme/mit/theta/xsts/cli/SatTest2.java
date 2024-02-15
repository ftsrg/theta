package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.collections.impl.RecursiveIntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint.GeneralizedSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeInitializer;
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

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class SatTest2 {

    public static void main(String[] args){

        MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

        ConstDecl<IntType> declX = Decls.Const("x", Int());
        ConstDecl<IntType> declXPrime = Decls.Const("x_prime", Int());
        ConstDecl<IntType> declY = Decls.Const("y", Int());
        ConstDecl<IntType> declYPrime = Decls.Const("y_prime", Int());
        ConstDecl<IntType> declZ = Decls.Const("z", Int());
        ConstDecl<IntType> declZPrime = Decls.Const("z_prime", Int());

        MddVariableOrder transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        MddVariable z_prime_trans = transOrder.createOnTop(MddVariableDescriptor.create(declZPrime, 0));
        MddVariable z_trans = transOrder.createOnTop(MddVariableDescriptor.create(declZ, 0));
        MddVariable y_prime_trans = transOrder.createOnTop(MddVariableDescriptor.create(declYPrime, 0));
        MddVariable y_trans = transOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
        MddVariable x_prime_trans = transOrder.createOnTop(MddVariableDescriptor.create(declXPrime, 0));
        MddVariable x_trans = transOrder.createOnTop(MddVariableDescriptor.create(declX, 0));

        MddVariableOrder stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        MddVariable z_state = stateOrder.createOnTop(MddVariableDescriptor.create(declZ, 0));
        MddVariable y_state = stateOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
        MddVariable x_state = stateOrder.createOnTop(MddVariableDescriptor.create(declX, 0));

        var transSig = transOrder.getDefaultSetSignature();
        var stateSig = stateOrder.getDefaultSetSignature();

        // x = 0, y = 0, z = 0
        Expr<BoolType> initExpr = And(Eq(declX.getRef(),Int(0)), Eq(declY.getRef(),Int(0)), Eq(declZ.getRef(),Int(0)));

        MddHandle initNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(initExpr, o -> (Decl) o, new SolverPool(Z3SolverFactory.getInstance())));

        // x' = y + 1, y' = z + 1, z' = z + 1, z' < 10
        Expr<BoolType> transExpr = And(And(Eq(declXPrime.getRef(),Add(declY.getRef(), Int(1))), Eq(declYPrime.getRef(), Add(declZ.getRef(), Int(1))), Eq(declZPrime.getRef(), Add(declZ.getRef(), Int(1)))), IntExprs.Lt(declZPrime.getRef(), Int(10)));

        var solverPool = new SolverPool(Z3SolverFactory.getInstance());
        MddHandle transitionNode = transSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(transExpr, o -> (Decl) o, solverPool));

        AbstractNextStateDescriptor nextStates = MddNodeNextStateDescriptor.of(transitionNode);

//        var relprod = new RelationalProductProvider(stateSig.getVariableOrder());
//        var relResult = relprod.compute(initNode, nextStates, stateSig.getTopVariableHandle());

//        var bfs = new BfsProvider(stateSig.getVariableOrder());
//        var bfsResult = bfs.compute(initNode, nextStates, stateSig.getTopVariableHandle());

        var saturation = new GeneralizedSaturationProvider(stateSig.getVariableOrder());
        var satResult = saturation.compute(new MddNodeInitializer(initNode), nextStates, stateSig.getTopVariableHandle());

        System.out.println(mddGraph.getUniqueTableSize());

        final Graph graph = new MddNodeVisualizer(SatTest2::nodeToString).visualize(satResult.getNode());
        try {
            GraphvizWriter.getInstance().writeFile(graph, "build\\mdd.dot");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

    }

    private static String nodeToString(MddNode node){
        if(node.getRepresentation() instanceof RecursiveIntObjMapViews.OfIntObjMapView<?,?>) return "";
        return node instanceof MddNode.Terminal ? ((MddNode.Terminal<?>) node).getTerminalData().toString() : node.getRepresentation().toString();
    }

}