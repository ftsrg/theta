package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.analysis.pred.*;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.*;
import hu.bme.mit.theta.xsts.dsl.XSTSVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslLexer;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class Old {

    try {
        XstsDslLexer lexer=new XstsDslLexer(CharStreams.fromFileName("src/test/resources/trafficlight.xsts"));
        CommonTokenStream tokenStream=new CommonTokenStream(lexer);
        XstsDslParser parser=new XstsDslParser(tokenStream);
        XstsDslParser.XstsContext model =parser.xsts();
        XSTSVisitor visitor=new XSTSVisitor();
        visitor.visitXsts(model);
        XSTS xsts=visitor.getXsts();

//            System.out.println(StmtUtils.toExpr(xsts.getEnvAction(), VarIndexing.all(0)).getExprs());
//            System.out.println(StmtUtils.toExpr(xsts.getEnvAction(), VarIndexing.all(0)).getIndexing());
        LTS<XstsState, XstsAction> lts= XstsLts.create(xsts);

        final ItpSolver solver = Z3SolverFactory.getInstace().createItpSolver();
        Logger logger = NullLogger.getInstance();

//            final Analysis<XstsState<ExplState>, XstsAction, ExplPrec> analysis = XstsAnalysis
//                    .create(ExplStmtAnalysis.create(solver, True()));
//            final ArgBuilder<XstsState<ExplState>, XstsAction, ExplPrec> argBuilder = ArgBuilder.create(lts,
//                    analysis, s -> ExprUtils.simplify(xsts.getProp(),s.getState().getVal()).equals(True()), true);
//            final Abstractor<XstsState<ExplState>, XstsAction, ExplPrec> abstractor = BasicAbstractor
//                    .builder(argBuilder)
//                    .waitlist(PriorityWaitlist.create(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.dfs())))
//                    .logger(logger).build();
//
//            Refiner<XstsState<ExplState>, XstsAction, ExplPrec> refiner = null;
//            refiner = SingleExprTraceRefiner.create(ExprTraceFwBinItpChecker.create(True(), True(), solver),
//                    JoiningPrecRefiner.create(new ItpRefToExplPrec()), logger);
//
//
//            final SafetyChecker<XstsState<ExplState>, XstsAction, ExplPrec> checker = CegarChecker
//                    .create(abstractor, refiner, logger);
//
//            final ExplPrec prec = ExplPrec.of(xsts.getVars());
//            System.out.println(prec.getVars());
//
//            SafetyResult res=checker.check(prec);
//            if(res.isUnsafe()){
//                System.out.println(res.asUnsafe().getTrace());
//            }
////            res.getArg().getNodes().forEach(System.out::println);
//            System.out.println(res.isSafe());

        PredAbstractors.PredAbstractor predAbstractor  = PredAbstractors.booleanAbstractor(solver);
        final Analysis<XstsState<PredState>, XstsAction, PredPrec> analysis = XstsAnalysis
                .create(PredAnalysis.create(solver, predAbstractor, True()));
        final ArgBuilder<XstsState<PredState>, XstsAction, PredPrec> argBuilder = ArgBuilder.create(lts,
                analysis, new XstsStatePredicate<ExprStatePredicate,PredState>(new ExprStatePredicate(xsts.getProp(), solver)), true);
        final Abstractor<XstsState<PredState>, XstsAction, PredPrec> abstractor = BasicAbstractor
                .builder(argBuilder)
                .stopCriterion(StopCriterions.firstCex()).logger(logger).build();

        ExprTraceChecker<ItpRefutation> exprTraceChecker = ExprTraceFwBinItpChecker.create(True(), xsts.getProp(), solver);

        Refiner<XstsState<PredState>, XstsAction, PredPrec> refiner = SingleExprTraceRefiner.create(exprTraceChecker,
                JoiningPrecRefiner.create(new ItpRefToPredPrec(ExprSplitters.whole())), logger);

        final SafetyChecker<XstsState<PredState>, XstsAction, PredPrec> checker = CegarChecker.create(abstractor, refiner,
                logger);

        final PredPrec prec = PredPrec.of();
        SafetyResult res=checker.check(prec);
        if(res.isUnsafe()){
            System.out.println(res.asUnsafe().getTrace());
        }
//            res.getArg().getNodes().forEach(System.out::println);
        System.out.println(res.isSafe());


    } catch (Exception e){
        e.printStackTrace();
    }

}
