package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.collections.impl.RecursiveIntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint.GeneralizedSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint.LegacyRelationalProductProvider;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.impl.OrNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeInitializer;
import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;

import java.io.*;
import java.util.*;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

public class XstsTest2 {

    public static void main(String[] args) throws IOException {

        final String filePath = "subprojects\\xsts\\xsts-analysis\\src\\test\\resources\\model\\trafficlight.xsts";
//        final String filePath = "C:\\Users\\Milan\\Desktop\\Vaganyut_synchronous.xsts";
        final String propPath = "subprojects\\xsts\\xsts-analysis\\src\\test\\resources\\property\\green_and_red.prop";

        final XSTS xsts;
        try (InputStream inputStream = new SequenceInputStream(new FileInputStream(filePath), /*new ByteArrayInputStream(("prop { " + "true" + " }").getBytes())*/ new FileInputStream(propPath))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }

        final MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

        final MddVariableOrder stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        final MddVariableOrder transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        final MddVariableOrder initOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        final NonDetStmt envTran = NonDetStmt.of(xsts.getEnv().getStmts().stream().flatMap(e -> xsts.getTran().getStmts().stream().map(t -> (Stmt) SequenceStmt.of(List.of(e, t)))).toList());
        final var envTranToExprResult = StmtUtils.toExpr(envTran, VarIndexingFactory.indexing(0));
        final var initToExprResult = StmtUtils.toExpr(xsts.getInit(), VarIndexingFactory.indexing(0));

        for (var v : xsts.getVars()) {
            stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0));

            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(envTranToExprResult.getIndexing().get(v) == 0 ? 1 : envTranToExprResult.getIndexing().get(v)), 0));
            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0));

            // TODO if indexes are identical, inject v'=v
            initOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(initToExprResult.getIndexing().get(v) == 0 ? 1 : initToExprResult.getIndexing().get(v)), 0));
            initOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), 0));
        }

        var stateSig = stateOrder.getDefaultSetSignature();
        var transSig = transOrder.getDefaultSetSignature();
        var initSig = initOrder.getDefaultSetSignature();

        final Expr<BoolType> initExpr = PathUtils.unfold(xsts.getInitFormula(), 0);
        MddHandle initNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(initExpr, o -> (Decl) o, new SolverPool(Z3SolverFactory.getInstance())));

        var initUnfold = PathUtils.unfold(initToExprResult.getExprs().stream().findFirst().get(), 0);
        final var initIdentityExprs = new ArrayList<Expr<BoolType>>();
        for (var v : xsts.getVars()) {
            if (initToExprResult.getIndexing().get(v) == 0)
                initIdentityExprs.add(Eq(v.getConstDecl(0).getRef(), v.getConstDecl(1).getRef()));
        }
        final var initExprWithIdentity = And(initUnfold, And(initIdentityExprs));
        MddHandle initTranNode = initSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(initExprWithIdentity, o -> (Decl) o, new SolverPool(Z3SolverFactory.getInstance())));
        AbstractNextStateDescriptor initNextState = MddNodeNextStateDescriptor.of(initTranNode);

        var rel = new LegacyRelationalProductProvider(stateSig.getVariableOrder());
        var initResult = rel.compute(initNode, initNextState, stateSig.getTopVariableHandle());

        final List<AbstractNextStateDescriptor> descriptors = new ArrayList<>();
        for (Stmt stmt : new ArrayList<>(envTran.getStmts())) {
            final var stmtToExpr = StmtUtils.toExpr(stmt, VarIndexingFactory.indexing(0));
            var stmtUnfold = PathUtils.unfold(stmtToExpr.getExprs().stream().findFirst().get(), 0);

            final var identityExprs = new ArrayList<Expr<BoolType>>();
            for (var v : xsts.getVars()) {
                if (stmtToExpr.getIndexing().get(v) < envTranToExprResult.getIndexing().get(v))
                    identityExprs.add(Eq(v.getConstDecl(stmtToExpr.getIndexing().get(v)).getRef(), v.getConstDecl(envTranToExprResult.getIndexing().get(v)).getRef()));
                if (envTranToExprResult.getIndexing().get(v) == 0)
                    identityExprs.add(Eq(v.getConstDecl(0).getRef(), v.getConstDecl(1).getRef()));
            }
            if (!identityExprs.isEmpty()) stmtUnfold = And(stmtUnfold, And(identityExprs));

            MddHandle transitionNode = transSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(stmtUnfold, o -> (Decl) o, new SolverPool(Z3SolverFactory.getInstance())));
            descriptors.add(MddNodeNextStateDescriptor.of(transitionNode));
        }
        AbstractNextStateDescriptor nextStates = OrNextStateDescriptor.create(descriptors);

        var gs = new GeneralizedSaturationProvider(stateSig.getVariableOrder());
        final MddHandle satResult = gs.compute(new MddNodeInitializer(initResult), nextStates, stateSig.getTopVariableHandle());
//        var satResult = gs.compute(initNode, nextStates, stateSig.getTopVariableHandle());

        final Expr<BoolType> negatedPropExpr = PathUtils.unfold(Not(xsts.getProp()), 0);
        final MddHandle propNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(negatedPropExpr, o -> (Decl) o, new SolverPool(Z3SolverFactory.getInstance())));

        final MddHandle propViolating = (MddHandle) satResult.intersection(propNode);

//        Long violatingSize = MddInterpreter.calculateNonzeroCount(propViolating);
//        System.out.println("States violating the property: " + violatingSize);

//        Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(satResult);
//        System.out.println("State space size: "+stateSpaceSize);

        System.out.println("Hit count: " + gs.getSaturateCache().getHitCount());
        System.out.println("Query count: " + gs.getSaturateCache().getQueryCount());
        System.out.println("Cache size: " + gs.getSaturateCache().getCacheSize());
//
        final Graph initGraph = new MddNodeVisualizer(XstsTest2::nodeToString).visualize(initResult.getNode());
        final Graph stateSpaceGraph = new MddNodeVisualizer(XstsTest2::nodeToString).visualize(satResult.getNode());
        final Graph violatingGraph = new MddNodeVisualizer(XstsTest2::nodeToString).visualize(propViolating.getNode());
        try {
            GraphvizWriter.getInstance().writeFile(initGraph, "build\\init.dot");
            GraphvizWriter.getInstance().writeFile(stateSpaceGraph, "build\\statespace.dot");
            GraphvizWriter.getInstance().writeFile(violatingGraph, "build\\violating.dot");
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

    private static String nodeToString(MddNode node) {
        if (node.getRepresentation() instanceof RecursiveIntObjMapViews.OfIntObjMapView<?, ?>)
            return "";
        return node instanceof MddNode.Terminal ? ((MddNode.Terminal<?>) node).getTerminalData().toString() : node.getRepresentation().toString();
    }

    private static String reverseString(String str) {
        StringBuilder sb = new StringBuilder(str);
        sb.reverse();
        return sb.toString();
    }

}
