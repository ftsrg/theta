package hu.bme.mit.theta.analysis.algorithm.symbolic.checker;

import hu.bme.mit.delta.collections.impl.RecursiveIntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint.GeneralizedSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeInitializer;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddNodeNextStateDescriptor;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;

import java.io.FileNotFoundException;
import java.util.List;
import java.util.Set;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

public class MddChecker<A extends ExprAction> implements SafetyChecker<MddWitness, MddCex, Void> {

    private final Expr<BoolType> initRel;
    private final VarIndexing initIndexing;
    private final A transRel;
    private final Expr<BoolType> safetyProperty;
    private final SolverFactory solverFactory;
    private final Logger logger;

    private MddChecker(Expr<BoolType> initRel,
                      VarIndexing initIndexing,
                      A transRel,
                      Expr<BoolType> safetyProperty,
                      SolverFactory solverFactory,
                      Logger logger) {
        this.initRel = initRel;
        this.initIndexing = initIndexing;
        this.transRel = transRel;
        this.safetyProperty = safetyProperty;
        this.solverFactory = solverFactory;
        this.logger = logger;
    }

    public static <A extends ExprAction> MddChecker<A> create(Expr<BoolType> initRel,
                                                                                                         VarIndexing initIndexing,
                                                                                                         A transRel,
                                                                                                         Expr<BoolType> safetyProperty,
                                                                                                         SolverFactory solverFactory,
                                                                                                         Logger logger) {
        return new MddChecker<A>(initRel, initIndexing, transRel, safetyProperty, solverFactory, logger);
    }

    @Override
    public SafetyResult<MddWitness, MddCex> check(Void input) {

        final MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

        final MddVariableOrder stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);
        final MddVariableOrder transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        final Set<VarDecl<?>> vars = ExprUtils.getVars(List.of(initRel, transRel.toExpr(), safetyProperty));
        for(var v : vars){
            final var domainSize = v.getType() instanceof BoolType ? 2 : 0;

            stateOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(initIndexing.get(v)), domainSize));

            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(transRel.nextIndexing().get(v)), domainSize));
            transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize));
        }

        final var stateSig = stateOrder.getDefaultSetSignature();
        final var transSig = transOrder.getDefaultSetSignature();

        final Expr<BoolType> initExpr = PathUtils.unfold(initRel, initIndexing);
        final MddHandle initNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(initExpr, o -> (Decl) o, new SolverPool(solverFactory)));

        final Expr<BoolType> transExpr = PathUtils.unfold(transRel.toExpr(), VarIndexingFactory.indexing(0));
        final MddHandle transitionNode = transSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(transExpr, o -> (Decl) o, new SolverPool(solverFactory)));
        final AbstractNextStateDescriptor nextStates = MddNodeNextStateDescriptor.of(transitionNode);

        final var gs = new GeneralizedSaturationProvider(stateSig.getVariableOrder());
        final MddHandle satResult = gs.compute(new MddNodeInitializer(initNode), nextStates, stateSig.getTopVariableHandle());

        final Expr<BoolType> negatedPropExpr = PathUtils.unfold(Not(safetyProperty), initIndexing);
        final MddHandle propNode = stateSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(negatedPropExpr, o -> (Decl) o, new SolverPool(solverFactory)));

        final MddHandle propViolating = (MddHandle) satResult.intersection(propNode);

        final Long violatingSize = MddInterpreter.calculateNonzeroCount(propViolating);
        System.out.println("States violating the property: " + violatingSize);

        final Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(satResult);
        System.out.println("State space size: "+stateSpaceSize);

        System.out.println("Hit count: "+gs.getSaturateCache().getHitCount());
        System.out.println("Query count: "+gs.getSaturateCache().getQueryCount());
        System.out.println("Cache size: "+gs.getSaturateCache().getCacheSize());
//
        final Graph stateSpaceGraph = new MddNodeVisualizer(MddChecker::nodeToString).visualize(satResult.getNode());
        final Graph violatingGraph = new MddNodeVisualizer(MddChecker::nodeToString).visualize(propViolating.getNode());
        try {
            GraphvizWriter.getInstance().writeFile(stateSpaceGraph, "build\\statespace.dot");
            GraphvizWriter.getInstance().writeFile(violatingGraph, "build\\violating.dot");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

        if(violatingSize != 0) return SafetyResult.unsafe(MddCex.of(propViolating),MddWitness.of(satResult));
        else return SafetyResult.safe(MddWitness.of(satResult));
    }

    private static String nodeToString(MddNode node){
        if(node.getRepresentation() instanceof RecursiveIntObjMapViews.OfIntObjMapView<?,?>) return "";
        return node instanceof MddNode.Terminal ? ((MddNode.Terminal<?>) node).getTerminalData().toString() : node.getRepresentation().toString();
    }
}
