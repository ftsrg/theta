package hu.bme.mit.theta.xcfa.explicit;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Edge;
import hu.bme.mit.theta.xcfa.explicit.util.ProcessTransitionCollector;
import hu.bme.mit.theta.xcfa.simulator.*;
import hu.bme.mit.theta.xcfa.simulator.partialorder.DependencyRelation;

import java.util.*;

/**
 * An explicit checker traversing every possible ordering of an XCFA state.
 * Supports only zero-initialized values (because of how ExplState works).
 */
public class PartialOrderExplicitChecker {

    private static class AmpleSetFactory {
        private final XCFA xcfa;
        // pre(Pi) I think
        private final Map<XCFA.Process, Collection<Transition>> allTransitionsByProcess;
        public AmpleSetFactory(XCFA xcfa) {
            this.xcfa = xcfa;
            allTransitionsByProcess = new HashMap<>();
            for (XCFA.Process process : xcfa.getProcesses()) {
                allTransitionsByProcess.put(process, ProcessTransitionCollector.getAllTransitionsByProcess(process));
            }
        }

        private void collectDependingProcesses(ProcessTransition t, Collection<XCFA.Process> alreadyProcessed,
                                               Collection<XCFA.Process> result) {
            for (var x : allTransitionsByProcess.entrySet()) {
                if (alreadyProcessed.contains(x.getKey())) {
                    continue;
                }
                if (x.getKey() == t.getProcess()) {
                    continue;
                }
                if (DependencyRelation.depends(t, x.getValue())) {
                    result.add(x.getKey());
                }
            }
        }

        // input is a non empty set of enabled transitions
        private Collection<Transition> collectAmpleSet(ExplState state, Collection<Transition> enabledTransitions) {
            HashSet<XCFA.Process> ampleSet = new HashSet<>();
            HashSet<XCFA.Process> notYetProcessed = new HashSet<>();


            HashMultimap<XCFA.Process, Transition> enabledTransitionsByProcess = HashMultimap.create();

            for (Transition pt : enabledTransitions) {
                if (!(pt instanceof ProcessTransition)) {
                    return enabledTransitions;
                }
                enabledTransitionsByProcess.put(((ProcessTransition) pt).getProcess(), pt);
            }

            // add a transition
            ProcessTransition first = (ProcessTransition) enabledTransitions.iterator().next();
            notYetProcessed.add(first.getProcess());
            // add dependencies transitively
            while (!notYetProcessed.isEmpty()) {
                XCFA.Process toBeProcessed = notYetProcessed.iterator().next();
                ampleSet.add(toBeProcessed);
                Collection<Transition> transitions = state.getTransitionsOfProcess(toBeProcessed);
                notYetProcessed.remove(toBeProcessed);
                for (Transition enabledTransition : enabledTransitionsByProcess.get(toBeProcessed)) {
                    collectDependingProcesses((ProcessTransition) enabledTransition, ampleSet, notYetProcessed);
                }
                // add disabled transitions' dependencies, which may activate the transition
                // more precisely: all processes' transitions that may enable
                // look at partialorder-test.xcfa for more information
                for (Transition tr : transitions) {
                    if (enabledTransitions.contains(tr)) {
                        continue;
                    }
                    // tr is disabled
                    if (!(tr instanceof ProcessTransition)) {
                        return enabledTransitions;
                    }
                    // tr is disabled ProcessTransition
                    collectDependingProcesses((ProcessTransition) tr, ampleSet, notYetProcessed);
                }
            }
            Collection<Transition> result = new HashSet<>();
            for (XCFA.Process p : ampleSet) {
                result.addAll(enabledTransitionsByProcess.get(p));
            }
            return result;
        }

        // Does not contain the logic of C3 about cycles
        public Collection<Transition> returnAmpleSet(ExplState expl) {
            Collection<Transition> enabled = expl.getEnabledTransitions();
            if (enabled.size() == 0) {
                return Collections.emptySet();
            }
            return collectAmpleSet(expl, enabled);
        }
    }

    private static class DfsNode {
        private final ExplState state;
        private Iterator<Transition> nextTransition;
        private final AmpleSetFactory factory;

        private DfsNode(ExplState state, AmpleSetFactory factory) {
            this.factory = factory;
            this.state = state;
            nextTransition = factory.returnAmpleSet(state).iterator();
        }

        public boolean hasChild() {
            return
                    isSafe() &&
                            !state.getSafety().finished &&
                            nextTransition.hasNext();
        }

        public boolean isSafe() {
            return state.getSafety().safe;
        }

        public DfsNode child() {
            Transition transition = nextTransition.next();
            return new DfsNode(state.executeTransition(transition), factory);
        }

        boolean expanded = false;

        public boolean isExplicitlyExpanded() { return expanded;}

        public void expandAll() {
            expanded = true;
            // With this code we forget what was already processed. (part of the ample set)
            // However, it is not a problem running the same transition twice
            // Because we store the states already processed
            nextTransition = state.getEnabledTransitions().iterator();
        }
    }

    public static class SafetyResult {
        public final boolean safe;
        public final String message;
        public final List<Transition> trace;
        private SafetyResult() {
            safe = true;
            message = null;
            trace = null;
        }
        private SafetyResult(ExplState.StateSafety base, List<Transition> trace) {
            Preconditions.checkArgument(!base.safe,
                    "SafetyResult should be built from an unsafe StateSafety");
            safe = base.safe;
            message = base.message;
            this.trace = trace;
        }

        @Override
        public String toString() {
            StringBuilder s = new StringBuilder();
            if (safe) {
                s.append("Safe");
            } else {
                s.append("Unsafe: ");
                s.append(message);
                s.append("\n");
                if (trace != null) {
                    for (Transition t : trace) {
                        s.append(t);
                        s.append("\n");
                    }
                }
            }
            return s.toString();
        }
    }

    /**
     * SafetyResult should be always unsafe OR finished.
     */
    public SafetyResult check(XCFA xcfa, boolean traced) {
        Set<AbstractExplState> exploredStates = new HashSet<>();
        Set<AbstractExplState> stackedStates = new HashSet<>();

        ExplState initialState;
        if (traced)
            initialState = new TracedExplState(xcfa);
        else
            initialState = new ExplState(xcfa);
        Stack<DfsNode> dfsStack = new Stack<>();
        dfsStack.push(new DfsNode(initialState, new AmpleSetFactory(xcfa)));
        while (!dfsStack.empty()) {
            DfsNode node = dfsStack.peek();
            if (node.hasChild()) {
                DfsNode child = node.child();
                //ImmutableExplState ies = child.state.toImmutableExplState();
                if (stackedStates.contains(child.state)) {
                    // TODO cycle. According to C3, we must expand the node
                    if (!node.isExplicitlyExpanded()) {
                        node.expandAll();
                        continue;
                    }
                }
                if (exploredStates.contains(child.state)) {
                    continue;
                }
                ImmutableExplState immutState = child.state.toImmutableExplState();
                exploredStates.add(immutState);
                stackedStates.add(immutState);
                dfsStack.push(child);
            } else {
                if (!node.isSafe()) {
                    return new SafetyResult(node.state.getSafety(), node.state.getTrace());
                }
                dfsStack.pop();
                stackedStates.remove(node.state);
            }
        }
        return new SafetyResult();
    }

}
