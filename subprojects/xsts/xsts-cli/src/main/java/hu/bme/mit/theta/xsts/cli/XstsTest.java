package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.collections.impl.RecursiveIntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint.*;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.impl.OrNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeNextStateDescriptor;
import hu.bme.mit.theta.analysis.utils.MddNodeCacheVisualizer;
import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
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
import hu.bme.mit.theta.frontend.petrinet.analysis.PtNetSystem;
import hu.bme.mit.theta.frontend.petrinet.analysis.VariableOrderingFactory;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import hu.bme.mit.theta.frontend.petrinet.pnml.PetriNetParser;
import hu.bme.mit.theta.frontend.petrinet.xsts.PetriNetToXSTS;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.util.*;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class XstsTest {

    public static void main(String[] args){

        final PetriNet petriNet;
        try {
            petriNet = PetriNetParser.loadPnml(new File("subprojects\\frontends\\petrinet-frontend\\petrinet-analysis\\src\\test\\resources\\dekker-15.pnml")).parsePTNet().get(0);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }

//        final List<Place> ordering = new ArrayList<>(petriNet.getPlaces());
//        ordering.sort((p1, p2) -> String.CASE_INSENSITIVE_ORDER.compare(reverseString(p1.getId()),
//                reverseString(p2.getId())
//        ));
        final List<Place> ordering;
        try {
            ordering = VariableOrderingFactory.fromFile("subprojects\\frontends\\petrinet-frontend\\petrinet-analysis\\src\\test\\resources\\dekker-15.pnml.gsat.order", petriNet);
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

        final Map<String, VarDecl> nameToDecl = new HashMap<>();
        xsts.getVars().forEach(v -> nameToDecl.put(v.getName(), v));
        Collections.reverse(ordering);
        for(var place : ordering){
            var v = nameToDecl.get(place.getId());
            stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0));

            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(toExprResult.getIndexing().get(v)), 0));
            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0));
        }

        var transSig = transOrder.getDefaultSetSignature();
        var stateSig = stateOrder.getDefaultSetSignature();

        MddHandle initNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(initExpr, o -> (Decl) o, new SolverPool(Z3SolverFactory.getInstance()::createSolver)));

        final List<AbstractNextStateDescriptor> descriptors = new ArrayList<>();
        final List<MddHandle> transitionHandles = new ArrayList<>();
//        final List<Stmt> stmts = new ArrayList<>();
//        for(int i = 0; i<25; i++) stmts.add(tran.getStmts().get(i));
        final var stmts = new ArrayList<>(tran.getStmts());
        for(Stmt stmt : stmts){
            final var stmtToExpr = StmtUtils.toExpr(stmt, VarIndexingFactory.indexing(0));
            var stmtUnfold = PathUtils.unfold(stmtToExpr.getExprs().stream().findFirst().get(), 0);

            final var identityExprs = new ArrayList<Expr<BoolType>>();
            for(var v : StmtUtils.getVars(tran)){
                if(stmtToExpr.getIndexing().get(v) < toExprResult.getIndexing().get(v)) identityExprs.add(Eq(v.getConstDecl(stmtToExpr.getIndexing().get(v)).getRef(),v.getConstDecl(toExprResult.getIndexing().get(v)).getRef()));
            }
            if(!identityExprs.isEmpty()) stmtUnfold = And(stmtUnfold, And(identityExprs));

            MddHandle transitionNode = transSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(stmtUnfold, o -> (Decl) o, new SolverPool(Z3SolverFactory.getInstance()::createSolver)));
            transitionHandles.add(transitionNode);
            descriptors.add(MddNodeNextStateDescriptor.of(transitionNode));
        }

        AbstractNextStateDescriptor nextStates = OrNextStateDescriptor.create(descriptors);

//        var relprod = new CursorRelationalProductProvider(stateSig.getVariableOrder());
//        var relResult = relprod.compute(initNode, nextStates, stateSig.getTopVariableHandle());
//
//        System.out.println(Z3SolverFactory.solversCreated);

//        var bfs = new BfsProvider(stateSig.getVariableOrder(), relprod);
//        var bfsResult = bfs.compute(initNode, nextStates, stateSig.getTopVariableHandle());

        final PtNetSystem system = new PtNetSystem(petriNet, ordering);

        final MddVariableOrder variableOrder = JavaMddFactory.getDefault().createMddVariableOrder(LatticeDefinition.forSets());
        ordering.forEach(p -> variableOrder.createOnTop(MddVariableDescriptor.create(p)));

        final GeneralizedSaturationProvider gs = new GeneralizedSaturationProvider(variableOrder);
        final MddHandle satResult = gs.compute(system.getInitializer(),
                system.getTransitions(),
                variableOrder.getDefaultSetSignature().getTopVariableHandle()
        );

//        var gs = new CursorGeneralizedSaturationProvider(stateSig.getVariableOrder());
//        var satResult = gs.compute(initNode, nextStates, stateSig.getTopVariableHandle());

        System.out.println(Z3SolverFactory.solversCreated);

        Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(satResult);
        System.out.println("State space size: "+stateSpaceSize);

        System.out.println("Hit count: "+gs.getSaturateCache().getHitCount());
        System.out.println("Query count: "+gs.getSaturateCache().getQueryCount());
        System.out.println("Cache size: "+gs.getSaturateCache().getCacheSize());
//
        final Graph graph = new MddNodeVisualizer(XstsTest::nodeToString).visualize(satResult.getNode());
        try {
            GraphvizWriter.getInstance().writeFile(graph, "build\\mdd.dot");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

//        int i = 0;
//        for(var handle: transitionHandles){
//            final Graph g = new MddNodeCacheVisualizer(XstsTest::nodeToString).visualize(handle.getNode());
//            try {
//                GraphvizWriter.getInstance().writeFile(g, "build\\tran"+ (i++) +".dot");
//            } catch (FileNotFoundException e) {
//                e.printStackTrace();
//            }
//        }

    }

    private static String nodeToString(MddNode node){
        if(node.getRepresentation() instanceof RecursiveIntObjMapViews.OfIntObjMapView<?,?>) return "";
        return node instanceof MddNode.Terminal ? ((MddNode.Terminal<?>) node).getTerminalData().toString() : node.getRepresentation().toString();
    }

    private static String reverseString(String str) {
        StringBuilder sb = new StringBuilder(str);
        sb.reverse();
        return sb.toString();
    }

}
