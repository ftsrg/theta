package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.zone.ClockPredPrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.prec.XtaPrec;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

public final class SingleXtaTraceRefiner <S extends ExprState, P extends Prec, R extends Refutation>
    implements Refiner<XtaState<Prod2State<S, ZoneState>>, XtaAction, XtaPrec<Prod2Prec<P, ClockPredPrec>>>
{

    private final XtaTraceChecker zoneTraceChecker;

    private final ExprTraceChecker<R> exprTraceChecker;
    private final PrecRefiner<XtaState<Prod2State<S, ZoneState>>, XtaAction, XtaPrec<Prod2Prec<P, ClockPredPrec>>, Prod2Refutation<R, ZoneRefutation>> precRefiner;
    private final PruneStrategy pruneStrategy;
    private final Logger logger;

    private final R emptyRefutation;



    private SingleXtaTraceRefiner(XtaTraceChecker zoneTraceChecker,
                                  ExprTraceChecker<R> exprTraceChecker,
                                  PrecRefiner<XtaState<Prod2State<S, ZoneState>>,
                                  XtaAction, XtaPrec<Prod2Prec<P, ClockPredPrec>>, Prod2Refutation<R, ZoneRefutation>> precRefiner,
                                  PruneStrategy pruneStrategy, Logger logger, R emptyRefutation) {
        this.zoneTraceChecker = zoneTraceChecker;
        this.exprTraceChecker = exprTraceChecker;
        this.precRefiner = precRefiner;
        this.pruneStrategy = pruneStrategy;
        this.logger = logger;
        this.emptyRefutation = emptyRefutation;
    }

    public static <S extends ExprState, P extends Prec,
            R extends Refutation> SingleXtaTraceRefiner create(XtaTraceChecker zoneTraceChecker,
                                                               ExprTraceChecker<R> exprTraceChecker,
                                                               PrecRefiner<XtaState<Prod2State<S, ZoneState>>,
                                                                       XtaAction, XtaPrec<Prod2Prec<P, ClockPredPrec>>, Prod2Refutation<R, ZoneRefutation>> precRefiner,
                                                               PruneStrategy pruneStrategy, Logger logger, R emptyRefutation){
    return new SingleXtaTraceRefiner<>(zoneTraceChecker, exprTraceChecker, precRefiner, pruneStrategy, logger, emptyRefutation);
                                                               }
    @Override
    public RefinerResult<XtaState<Prod2State<S, ZoneState>>, XtaAction, XtaPrec<Prod2Prec<P, ClockPredPrec>>> refine(ARG<XtaState<Prod2State<S, ZoneState>>, XtaAction> arg, XtaPrec<Prod2Prec<P, ClockPredPrec>> prec) {
        checkNotNull(arg);
        checkNotNull(prec);
        assert !arg.isSafe() : "ARG must be unsafe";

        Optional<ArgTrace<XtaState<Prod2State<S, ZoneState>>, XtaAction>> optionalNewCex = arg.getCexs().filter(cex -> ArgCexCheckHandler.instance.checkIfCounterexampleNew(cex)).findFirst();
        final ArgTrace<XtaState<Prod2State<S, ZoneState>>, XtaAction> cexToConcretize = optionalNewCex.get();

        List<ZoneState> zoneStates = cexToConcretize.nodes().stream().map(ArgNode::getState).map(XtaState::getState).map(Prod2State::getState2).collect(Collectors.toList());
        List<XtaAction> actions = cexToConcretize.edges().stream().map(ArgEdge::getAction).toList();
        List<XtaAction> zoneActions = actions;
        ArrayList<XtaAction> exprActions = new ArrayList<XtaAction>();
        for(final XtaAction action : actions){

            exprActions.add(action.pruneClocks());
        }
        List<S> exprStates = cexToConcretize.nodes().stream().map(ArgNode::getState).map(XtaState::getState).map(Prod2State::getState1).collect(Collectors.toList());

        final Trace<ZoneState, XtaAction> zoneTrace = Trace.of(zoneStates, zoneActions);
        final Trace<S, XtaAction> exprTrace = Trace.of(exprStates, exprActions);


        final ExprTraceStatus<ZoneRefutation> cexZoneStatus = zoneTraceChecker.check(zoneTrace);

        final ExprTraceStatus<R> cexExprStatus = exprTraceChecker.check(exprTrace);

        final Trace<XtaState<Prod2State<S, ZoneState>>, XtaAction> traceToConcretize = cexToConcretize.toTrace();
        logger.write(Logger.Level.INFO, "|  |  Trace length: %d%n", traceToConcretize.length());
        logger.write(Logger.Level.DETAIL, "|  |  Trace: %s%n", traceToConcretize);

        logger.write(Logger.Level.SUBSTEP, "|  |  Checking trace...");

        //final ExprTraceStatus<ZoneRefutation> cexStatus = exprTraceChecker.check(traceToConcretize);
        logger.write(Logger.Level.SUBSTEP, "done, result: %s%n", cexZoneStatus);
        logger.write(Logger.Level.SUBSTEP, "done, result: %s%n", cexExprStatus);

        assert cexZoneStatus.isFeasible() || cexZoneStatus.isInfeasible() : "Unknown CEX status";
        assert cexExprStatus.isFeasible() || cexExprStatus.isInfeasible() : "Unknown CEX status";

        if (cexZoneStatus.isFeasible() && cexExprStatus.isFeasible()) { // if any of traces are feasible than it is unsafe
            return RefinerResult.unsafe(traceToConcretize);
        } else {
            final ZoneRefutation zoneRefutation =cexZoneStatus.isInfeasible() ? cexZoneStatus.asInfeasible().getRefutation() : ZoneRefutation.emptyRefutation();
            final R exprRefutation = cexExprStatus.isInfeasible() ? cexExprStatus.asInfeasible().getRefutation() : emptyRefutation;
            logger.write(Logger.Level.DETAIL, "|  |  |  Refutation: %s%n", zoneRefutation);
            logger.write(Logger.Level.DETAIL, "|  |  |  Refutation: %s%n", exprRefutation);

            Prod2Refutation<R, ZoneRefutation> prod2Refutation = new Prod2Refutation<R, ZoneRefutation>(exprRefutation, zoneRefutation);

            final XtaPrec<Prod2Prec<P, ClockPredPrec>> refinedPrec = precRefiner.refine(prec, traceToConcretize, prod2Refutation);
            final int pruneIndex = prod2Refutation.getPruneIndex();
            assert 0 <= pruneIndex : "Pruning index must be non-negative";
            assert pruneIndex <= cexToConcretize.length() : "Pruning index larger than cex length";

            ArgCexCheckHandler.instance.addCounterexample(cexToConcretize);

            switch (pruneStrategy) {
                case LAZY:
                    logger.write(Logger.Level.SUBSTEP, "|  |  Pruning from index %d...", pruneIndex);
                    final ArgNode<XtaState<Prod2State<S, ZoneState>>, XtaAction> nodeToPrune = cexToConcretize.node(pruneIndex);
                    arg.prune(nodeToPrune);

                    break;
                case FULL:
                    logger.write(Logger.Level.SUBSTEP, "|  |  Pruning whole ARG", pruneIndex);
                    arg.pruneAll();
                    break;
                default:
                    throw new UnsupportedOperationException("Unsupported pruning strategy");
            }
            logger.write(Logger.Level.SUBSTEP, "done%n");

            return RefinerResult.spurious(refinedPrec);
        }
    }

}
