package hu.bme.mit.theta.xsts.analysis.concretizer;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.XstsAction;
import hu.bme.mit.theta.xsts.analysis.XstsState;
import org.checkerframework.checker.units.qual.A;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public final class TraceGenerationXstsTraceConcretizerUtil {
    private static final List<Tuple2<List<XstsState<ExplState>>, ItpRefutation>> infeasibles = new ArrayList<>();
    private static String report = null;
    private static boolean foundInfeasible = false;

    private TraceGenerationXstsTraceConcretizerUtil() {
    }

    public static Set<XstsStateSequence> concretizeTraceSet(List<Trace<XstsState<ExplState>, XstsAction>> abstractTraces, SolverFactory solverFactory, final XSTS xsts) {
        final VarFilter varFilter = VarFilter.of(xsts);
        final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(xsts.getInitFormula(),
                Bool(true), solverFactory.createItpSolver());
        HashMap<Trace<XstsState<ExplState>, XstsAction>, XstsStateSequence> tracePairs = new HashMap<>();

        for (Trace<XstsState<ExplState>, XstsAction> abstractTrace : abstractTraces) {
            // another xsts specific thing - if the env is more complicated, trace might end in env sending something, which might seem weird
            XstsState<ExplState> lastState = abstractTrace.getStates().get(abstractTrace.getStates().size() - 1);
            if(lastState.toString().contains("last_env")) {
                abstractTrace = shortenTrace(abstractTrace, abstractTrace.getStates().size()-2);
            }

            ExprTraceStatus<ItpRefutation> status = checker.check(abstractTrace);
            if(status.isInfeasible()) {
                foundInfeasible = true;
                addToReport(status.asInfeasible().getRefutation(), abstractTrace);
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

                tracePairs.put(abstractTrace, concretizedTrace);
            }
        }

        // if trace was shortened, it might match with another one, in this case, do not add it again
        HashMap<Trace<XstsState<ExplState>, XstsAction>, XstsStateSequence> filteredTracePairs = new HashMap<>();
        tracePairs.keySet().stream().filter(trace -> {
            for (Trace<XstsState<ExplState>, XstsAction> otherTrace : tracePairs.keySet()) {
                if(trace.getStates().size() < otherTrace.getStates().size()) {
                    String traceString = trace.toString();
                    String traceStringWithoutClosingParentheses = traceString.substring(0, traceString.length()-1);
                    if(otherTrace.toString().contains(traceStringWithoutClosingParentheses)) {
                        return false;
                    }
                }
            }
            return true;
        }).forEach(key -> filteredTracePairs.put(key, tracePairs.get(key)));

        createReport(filteredTracePairs.keySet());
        return new HashSet<XstsStateSequence>(filteredTracePairs.values());
    }

    private static void addToReport(ItpRefutation refutation, Trace<XstsState<ExplState>, XstsAction> abstractTrace) {
        ArrayList<XstsState<ExplState>> prunedStates = new ArrayList<>();
        for(int i = refutation.getPruneIndex()+1; i < abstractTrace.getStates().size(); i++) {
            if(abstractTrace.getState(i).toString().contains("last_internal")) { // xsts specific condition
                prunedStates.add(abstractTrace.getState(i));
            }
        }
        infeasibles.add(Tuple2.of(prunedStates, refutation));
        System.out.println(refutation.get(refutation.getPruneIndex()));
    }

    private static void createReport(Collection<Trace<XstsState<ExplState>, XstsAction>> traces) {
        Set<XstsState<ExplState>> statesVisited = traces.stream().map(Trace::getStates).flatMap(List::stream).collect(Collectors.toSet());
        // xsts specific part
        statesVisited = statesVisited.stream().filter(state -> state.toString().contains("last_internal")).collect(Collectors.toSet());

        List<XstsState<ExplState>> missingStates = new ArrayList<>();
        List<ItpRefutation> stateRefutations = new ArrayList<>();
        for (Tuple2<List<XstsState<ExplState>>, ItpRefutation> infeasible : infeasibles) {
            boolean missingState = false;
            for (XstsState<ExplState> xstsState : infeasible.get1()) {
                if (!stateContains(statesVisited, xstsState)) {
                    missingState = true;
                    missingStates.add(xstsState);
                }
            }
            if(missingState) {
                stateRefutations.add(infeasible.get2());
            }
        }

        Set<VarDecl<?>> problematicVariables = stateRefutations.stream().map(refutation -> ExprUtils.getVars(refutation.get(refutation.getPruneIndex()))).flatMap(Set::stream).collect(Collectors.toSet());

        StringBuilder reportBuilder = new StringBuilder();

        // allapot fedest pontosan nezzuk, transition fedest csak annyira, hogy serulhetett-e
        if(foundInfeasible) {
            reportBuilder.append("There were infeasible traces found; transition coverage might be incomplete\n");
        }

        if(stateRefutations.isEmpty()) {
            reportBuilder.append("State coverage (including variables in variable list) is complete\n");
        } else {
            reportBuilder.append("State coverage (including variables in variable list) is incomplete.\n\n");

            reportBuilder.append("The following abstract states are not covered (they might or might not be possible):\n");

            for (XstsState<ExplState> missingState : missingStates) {
                reportBuilder.append(missingState.toString());
                reportBuilder.append("\n------------------------------\n");
            }

            reportBuilder.append("\n");
            // TODO ez NAGYON heurisztika, pl ha prioritas miatt maradt ki valami, akkor hulyesegeket is mondhat
            reportBuilder.append("Maybe adding some of the following variables to the variable list can help:\n");
            reportBuilder.append(problematicVariables.stream().map(Decl::getName).collect(Collectors.toSet()));
            reportBuilder.append("\n");
        }

        report = reportBuilder.toString();
    }

    private static boolean stateContains(Set<XstsState<ExplState>> statesVisited, XstsState<ExplState> xstsState) {
        StringBuilder sb1 = new StringBuilder();
        List<String> stateLineList = Arrays.asList(xstsState.toString().split("\n"));
        for (String line : stateLineList) {
            if (!line.contains("__id_")) {
                sb1.append(line);
                sb1.append("\n");
            }
        }
        String xstsStateNoTransitions = sb1.toString();

        List<String> statesVisitedNoTransitions = statesVisited.stream().map(state -> {
            StringBuilder sb = new StringBuilder();
            List<String> lineList = Arrays.asList(state.toString().split("\n"));
            for (String line : lineList) {
                if (!line.contains("__id_")) {
                    sb.append(line);
                    sb.append("\n");
                }
            }
            return sb.toString();
        }).toList();

        return statesVisitedNoTransitions.contains(xstsStateNoTransitions);
    }

    private static Trace<XstsState<ExplState>, XstsAction> shortenTrace(Trace<XstsState<ExplState>, XstsAction> abstractTrace, int pruneIndex) {
        List<XstsState<ExplState>> newStates = new ArrayList<>(abstractTrace.getStates());
        newStates = newStates.subList(0, pruneIndex+1);
        List<XstsAction> newActions = new ArrayList<>(abstractTrace.getActions());
        newActions = newActions.subList(0, pruneIndex);
        abstractTrace = Trace.of(newStates, newActions); // remove last state
        return abstractTrace;
    }

    public static String getReport() {
        return report;
    }
}