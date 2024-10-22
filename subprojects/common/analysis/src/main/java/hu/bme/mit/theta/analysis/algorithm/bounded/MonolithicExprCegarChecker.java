package hu.bme.mit.theta.analysis.algorithm.bounded;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.*;
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
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.SolverFactory;

import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

public class MonolithicExprCegarChecker<W extends Witness, S extends ExprState, A extends ExprAction, P extends Prec> implements SafetyChecker<W, Trace<S, A>, PredPrec> {
    private final MonolithicExpr model;
    private final Function<MonolithicExpr, SafetyChecker<W, ? extends Trace<? extends ExprState, ? extends ExprAction>, UnitPrec>> checkerFactory;

    private final Function<Valuation, S> valToState;
    private final BiFunction<Valuation, Valuation, A> biValToAction;

    private final SolverFactory solverFactory;

    private final Logger logger;
    public MonolithicExprCegarChecker(MonolithicExpr model,
                                      Function<MonolithicExpr, SafetyChecker<W, ? extends Trace<? extends ExprState, ? extends ExprAction>, UnitPrec>> checkerFactory,
                                      Function<Valuation, S> valToState, BiFunction<Valuation, Valuation, A> biValToAction, Logger logger, SolverFactory solverFactory
    ) {
        this.model=model;
        this.checkerFactory=checkerFactory;
        this.valToState = valToState;
        this.biValToAction = biValToAction;
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
                final Trace<? extends ExprState, ? extends ExprAction> trace = result.asUnsafe().getCex();

                final ExprTraceChecker<ItpRefutation> exprTraceFwBinItpChecker = ExprTraceFwBinItpChecker.create(model.getInitExpr(), Not(model.getPropExpr()), solverFactory.createItpSolver());

                if(trace != null){
                    final ExprTraceStatus<ItpRefutation> concretizationResult = exprTraceFwBinItpChecker.check(trace);
                    if(concretizationResult.isFeasible()){
                        logger.write(Logger.Level.INFO, "Model is unsafe, stopping CEGAR");

                        final var valTrace = concretizationResult.asFeasible().getValuations();
                        Valuation lastValuation = null;
                        final ArrayList<S> states = new ArrayList<>();
                        final ArrayList<A> actions = new ArrayList<>();
                        for(var val : valTrace.getStates()){
                            states.add(valToState.apply(val));
                            if(lastValuation != null){
                                actions.add(biValToAction.apply(lastValuation, val));
                            }
                            lastValuation = val;
                        }

                        return SafetyResult.unsafe(Trace.of(states, actions), result.getWitness());
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
