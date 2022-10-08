package hu.bme.mit.theta.xsts.analysis.concretizer;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.XstsAction;
import hu.bme.mit.theta.xsts.analysis.XstsState;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public final class TraceGenerationXstsTraceConcretizerUtil {

    private TraceGenerationXstsTraceConcretizerUtil() {
    }

    public static Set<XstsStateSequence> concretizeTraceSet(List<Trace<XstsState<?>, XstsAction>> abstractTraces, SolverFactory solverFactory, final XSTS xsts) {
        final VarFilter varFilter = VarFilter.of(xsts);
        final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(xsts.getInitFormula(),
                Bool(true), solverFactory.createItpSolver());
        Set<XstsStateSequence> concretizedTraces = new HashSet<>();

        for (Trace<XstsState<?>, XstsAction> abstractTrace : abstractTraces) {
            ExprTraceStatus<ItpRefutation> status = checker.check(abstractTrace);
            if(status.isInfeasible()) {
                int pruneIndex = status.asInfeasible().getRefutation().getPruneIndex();
                if(pruneIndex>0) {
                    abstractTrace = shortenTrace(abstractTrace, pruneIndex);
                    status = checker.check(abstractTrace);
                }
            }
            if(status.isFeasible()) {
                final Trace<Valuation, ? extends Action> valuations = status.asFeasible().getValuations();
                assert valuations.getStates().size() == abstractTrace.getStates().size();
                final List<XstsState<ExplState>> xstsStates = new ArrayList<>();
                for (int i = 0; i < abstractTrace.getStates().size(); ++i) {
                    xstsStates.add(XstsState.of(ExplState.of(varFilter.filter(valuations.getState(i))), abstractTrace.getState(i).lastActionWasEnv(), abstractTrace.getState(i).isInitialized()));
                }

                XstsStateSequence concretizedTrace = XstsStateSequence.of(xstsStates, xsts);
                // if trace was shortened, it might match with another one, in this case, do not add it again
                if(concretizedTraces.stream().noneMatch(xstsStateSequence -> xstsStateSequence.toString().equals(concretizedTrace.toString()))) {
                    concretizedTraces.add(concretizedTrace);
                }
            }
        }
        return concretizedTraces;
    }

    private static Trace<XstsState<?>, XstsAction> shortenTrace(Trace<XstsState<?>, XstsAction> abstractTrace, int pruneIndex) {
        List<XstsState<?>> newStates = new ArrayList<>(abstractTrace.getStates());
        newStates = newStates.subList(0, pruneIndex+1);
        List<XstsAction> newActions = new ArrayList<>(abstractTrace.getActions());
        newActions = newActions.subList(0, pruneIndex);
        abstractTrace = Trace.of(newStates, newActions); // remove last state
        return abstractTrace;
    }

    private static XstsStateSequence concretize(
        Trace<XstsState<?>, XstsAction> trace, SolverFactory solverFactory, final XSTS xsts) {

        final VarFilter varFilter = VarFilter.of(xsts);
        final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(xsts.getInitFormula(),
                Bool(true), solverFactory.createItpSolver());

        ExprTraceStatus<ItpRefutation> status = checker.check(trace);
        while(status.isInfeasible() && trace.length()>0) {
            List<XstsState<?>> newStates = new ArrayList<>(trace.getStates());
            newStates.remove(trace.getStates().size() - 1);
            List<XstsAction> newActions = new ArrayList<>(trace.getActions());
            newActions.remove(trace.getActions().size()-1);
            trace = Trace.of(newStates, newActions); // remove last state
            status = checker.check(trace);
        }
        if(trace.length()==0) {
            return null;
        }
        final Trace<Valuation, ? extends Action> valuations = status.asFeasible().getValuations();
        assert valuations.getStates().size() == trace.getStates().size();
        final List<XstsState<ExplState>> xstsStates = new ArrayList<>();
        for (int i = 0; i < trace.getStates().size(); ++i) {
            xstsStates.add(XstsState.of(ExplState.of(varFilter.filter(valuations.getState(i))), trace.getState(i).lastActionWasEnv(), trace.getState(i).isInitialized()));
        }

        return XstsStateSequence.of(xstsStates, xsts);
    }
}