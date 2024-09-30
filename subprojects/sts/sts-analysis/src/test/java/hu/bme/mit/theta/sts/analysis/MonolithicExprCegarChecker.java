package hu.bme.mit.theta.sts.analysis;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.bounded.AbstractMonolithicExpr;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import org.junit.Assert;

import java.util.List;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

public class MonolithicExprCegarChecker<S extends ExprState, A extends ExprAction, P extends PredPrec> implements SafetyChecker<S,A,P> {
    private MonolithicExpr model;
    private Function<MonolithicExpr, SafetyChecker<S, A, UnitPrec>> checkerFactory;

    private Logger logger;
    public MonolithicExprCegarChecker(MonolithicExpr model, Function<MonolithicExpr, SafetyChecker<S, A, UnitPrec>> checkerFactory, Logger logger) {
        this.model=model;
        this.checkerFactory=checkerFactory;
        this.logger=logger;
    }
    public SafetyResult<S,A> check(P initPrec){
        var predPrec = initPrec == null ? PredPrec.of(List.of(model.init(), model.prop())) : initPrec;

        while(true){
            final var abstractMonolithicExpr = new AbstractMonolithicExpr(model ,predPrec);
            final var checker = checkerFactory.apply(abstractMonolithicExpr);

            final var result = checker.check();
            if(result.isSafe()) {
                logger.write(Logger.Level.INFO, "Model is safe, stopping CEGAR");
                return SafetyResult.safe();
            } else {
                Assert.assertEquals(false, result.isSafe());
                final Trace<S, A> trace = result.asUnsafe().getTrace();

                final ExprTraceChecker<ItpRefutation> exprTraceFwBinItpChecker = ExprTraceFwBinItpChecker.create(model.init(), Not(model.prop()), Z3SolverFactory.getInstance().createItpSolver());

                if(trace != null){
                    final ExprTraceStatus<ItpRefutation> concretizationResult = exprTraceFwBinItpChecker.check(trace);
                    if(concretizationResult.isFeasible()){
                        logger.write(Logger.Level.INFO, "Model is unsafe, stopping CEGAR");
                        return SafetyResult.unsafe(trace);
                    }else{
                        final var ref = concretizationResult.asInfeasible().getRefutation();
                        final var newPred = ref.get(ref.getPruneIndex());
                        final var newPrec = PredPrec.of(newPred);
                        predPrec= predPrec.join(newPrec);
                        logger.write(Logger.Level.INFO, "Added new predicate "+ newPrec);
                    }
                }
            }
        }
    }

}
