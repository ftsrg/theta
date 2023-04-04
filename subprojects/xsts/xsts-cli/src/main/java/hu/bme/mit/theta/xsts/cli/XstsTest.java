package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.collections.impl.RecursiveIntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint.*;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeNextStateDescriptor;
import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.BasicVarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import hu.bme.mit.theta.frontend.petrinet.pnml.PetriNetParser;
import hu.bme.mit.theta.frontend.petrinet.xsts.PetriNetToXSTS;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.util.List;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class XstsTest {

    public static void main(String[] args){

        final PetriNet petriNet;
        try {
            petriNet = PetriNetParser.loadPnml(new File("subprojects\\frontends\\petrinet-frontend\\petrinet-analysis\\src\\test\\resources\\simple.pnml")).parsePTNet().get(0);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        final XSTS xsts = PetriNetToXSTS.createXSTS(petriNet, null);

        final Expr<BoolType> initExpr = PathUtils.unfold(xsts.getInitFormula(), 0);

        MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

        MddVariableOrder stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        MddVariableOrder transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        final NonDetStmt tran = xsts.getTran();
        final var toExprResult = StmtUtils.toExpr(tran, VarIndexingFactory.indexing(0));
        final var unfoldResult = PathUtils.unfold(toExprResult.getExprs().stream().findFirst().get(), 0);
        for(var v : xsts.getVars()){
            stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0));

            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(toExprResult.getIndexing().get(v)), 0));
            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0));
        }

        var transSig = transOrder.getDefaultSetSignature();
        var stateSig = stateOrder.getDefaultSetSignature();

        MddHandle initNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(initExpr, o -> (Decl) o, new SolverPool(Z3SolverFactory.getInstance()::createSolver)));

        MddHandle transitionNode = transSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(unfoldResult, o -> (Decl) o, new SolverPool(Z3SolverFactory.getInstance()::createSolver)));
        AbstractNextStateDescriptor nextStates = MddNodeNextStateDescriptor.of(transitionNode);

//        var relprod = new CursorRelationalProductProvider(stateSig.getVariableOrder());
//        var relResult = relprod.compute(initNode, nextStates, stateSig.getTopVariableHandle());
//
//        System.out.println(Z3SolverFactory.solversCreated);

//        var bfs = new BfsProvider(stateSig.getVariableOrder(), relprod);
//        var bfsResult = bfs.compute(initNode, nextStates, stateSig.getTopVariableHandle());

        var saturation = new CursorGeneralizedSaturationProvider(stateSig.getVariableOrder());
        var satResult = saturation.compute(initNode, nextStates, stateSig.getTopVariableHandle());

        System.out.println(Z3SolverFactory.solversCreated);
//
        final Graph graph = new MddNodeVisualizer(XstsTest::nodeToString).visualize(satResult.getNode());
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
