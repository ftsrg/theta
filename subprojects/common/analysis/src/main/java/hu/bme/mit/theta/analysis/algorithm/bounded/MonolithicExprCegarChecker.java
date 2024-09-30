package hu.bme.mit.theta.analysis.algorithm.bounded;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.Witness;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;

import java.util.List;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

public class MonolithicExprCegarChecker<W extends Witness, S extends ExprState, A extends ExprAction, P extends Prec> implements SafetyChecker<W, Trace<S, A>, PredPrec> {
    private final MonolithicExpr model;
    private final Function<MonolithicExpr, SafetyChecker<W, Trace<S, A>, P>> checkerFactory;

    private final SolverFactory solverFactory;

    private final Logger logger;
    public MonolithicExprCegarChecker(MonolithicExpr model, Function<MonolithicExpr, SafetyChecker<W, Trace<S, A>, P>> checkerFactory, Logger logger, SolverFactory solverFactory) {
        this.model=model;
        this.checkerFactory=checkerFactory;
        this.logger=logger;
        this.solverFactory = solverFactory;
    }
    public SafetyResult<W ,Trace<S, A>> check(PredPrec initPrec){
        var predPrec = initPrec == null ? PredPrec.of(List.of(model.getInitExpr(), model.getPropExpr())) : initPrec;

        while(true){
            final var abstractMonolithicExpr = AbstractMonolithicExprKt.createAbstract(model, predPrec);
            final var checker = checkerFactory.apply(abstractMonolithicExpr);

            final var result = checker.check();
            if(result.isSafe()) {
                logger.write(Logger.Level.INFO, "Model is safe, stopping CEGAR");
                return SafetyResult.safe(result.getWitness());
            } else {
                Preconditions.checkState(result.isUnsafe());
                final Trace<S, A> trace = result.asUnsafe().getCex();

                final ExprTraceChecker<ItpRefutation> exprTraceFwBinItpChecker = ExprTraceFwBinItpChecker.create(model.getInitExpr(), Not(model.getPropExpr()), solverFactory.createItpSolver());

                if(trace != null){
                    final ExprTraceStatus<ItpRefutation> concretizationResult = exprTraceFwBinItpChecker.check(trace);
                    if(concretizationResult.isFeasible()){
                        logger.write(Logger.Level.INFO, "Model is unsafe, stopping CEGAR");
                        return SafetyResult.unsafe(trace, result.getWitness());
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
