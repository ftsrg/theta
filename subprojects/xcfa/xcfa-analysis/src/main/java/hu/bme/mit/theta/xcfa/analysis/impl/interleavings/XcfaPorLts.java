/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import hu.bme.mit.theta.analysis.algorithm.PorLts;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.*;
import java.util.stream.Collectors;

public class XcfaPorLts extends PorLts<XcfaState<?>, XcfaAction, XcfaEdge> {

    private final XCFA xcfa;

    private final XcfaLts simpleXcfaLts = new XcfaLts();

    private final Random random = new Random();

    public XcfaPorLts(XCFA xcfa) {
        this.xcfa = xcfa;
        collectBackwardTransitions();
    }

    @Override
    protected Collection<XcfaAction> getAllEnabledActionsFor(XcfaState<?> state) {
        return simpleXcfaLts.getEnabledActionsFor(state);
    }

    @Override
    protected Collection<XcfaAction> getPersistentSetFirstActions(
        Collection<XcfaAction> allEnabledActions) {
        var enabledActionsByProcess = allEnabledActions.stream()
            .collect(Collectors.groupingBy(XcfaAction::getProcess));
        List<Integer> enabledProcesses = new ArrayList<>(enabledActionsByProcess.keySet());
        Collections.shuffle(enabledProcesses);
        Collection<XcfaAction> firstActions = new HashSet<>();

        for (Integer enabledProcess : enabledProcesses) {
            var actionsByProcess = enabledActionsByProcess.get(enabledProcess);
            firstActions.add(actionsByProcess.get(random.nextInt(actionsByProcess.size())));
        }
        return firstActions;
    }

    @Override
    protected boolean canEnOrDisableEachOther(XcfaAction action1, XcfaAction action2) {
        return action1.getProcess().equals(action2.getProcess());
    }

    @Override
    protected XcfaEdge getTransitionOf(XcfaAction action) {
        return action.getEdge();
    }

    @Override
    protected Set<XcfaEdge> getSuccessiveTransitions(XcfaEdge edge) {
        var outgoingEdges = new HashSet<>(edge.getTarget().getOutgoingEdges());
        List<XcfaLabel.StartThreadXcfaLabel> startThreads = edge.getLabels().stream()
            .filter(label -> label instanceof XcfaLabel.StartThreadXcfaLabel)
            .map(label -> (XcfaLabel.StartThreadXcfaLabel) label).collect(Collectors.toList());
        if (startThreads.size()
            > 0) { // for start thread labels, the thread procedure must be explored, too!
            startThreads.forEach(startThread ->
                outgoingEdges.addAll(
                    startThread.getProcess().getMainProcedure().getInitLoc().getOutgoingEdges()));
        }
        return outgoingEdges;
    }

    /**
     * Returns the global variables that an edge uses (it is present in one of its labels).
     *
     * @param edge whose global variables are to be returned
     * @return the set of used global variables
     */
    @Override
    protected Set<VarDecl<? extends Type>> getDirectlyUsedSharedObjects(XcfaEdge edge) {
        Set<VarDecl<?>> vars = new HashSet<>();
        edge.getLabels().forEach(label -> LabelUtils.getVars(label).forEach(usedVar -> {
            if (xcfa.getGlobalVars().contains(usedVar)) {
                vars.add(usedVar);
            }
        }));
        return vars;
    }

    /**
     * Returns the global variables that an edge uses or if it is the start of an atomic block the
     * global variables that are used in the atomic block.
     *
     * @param edge whose global variables are to be returned
     * @return the set of directly or indirectly used global variables
     */
    @Override
    protected Set<? extends Decl<? extends Type>> getUsedSharedObjects(XcfaEdge edge) {
        Set<? extends Decl<? extends Type>> vars;
        var labels = edge.getLabels();
        if (labels.stream().anyMatch(label -> label instanceof XcfaLabel.AtomicBeginXcfaLabel)) {
            vars = getSharedObjectsWithBFS(edge, xcfaEdge -> xcfaEdge.getLabels().stream()
                .noneMatch(label -> label instanceof XcfaLabel.AtomicEndXcfaLabel));
        } else {
            vars = getDirectlyUsedSharedObjects(edge);
        }
        return vars;
    }

    /**
     * Collects backward edges of the given XCFA.
     */
    @Override
    protected void collectBackwardTransitions() {
        for (var process : xcfa.getProcesses()) {
            for (var procedure : process.getProcedures()) {
                // DFS for every procedure of the XCFA to discover backward edges
                Set<XcfaLocation> visitedLocations = new HashSet<>();
                Stack<XcfaLocation> stack = new Stack<>();

                stack.push(
                    procedure.getInitLoc()); // start from the initial location of the procedure
                while (!stack.isEmpty()) {
                    XcfaLocation visiting = stack.pop();
                    visitedLocations.add(visiting);
                    for (var outgoingEdge : visiting.getOutgoingEdges()) {
                        var target = outgoingEdge.getTarget();
                        if (visitedLocations.contains(target)) { // backward edge
                            backwardTransitions.add(outgoingEdge);
                        } else {
                            stack.push(target);
                        }
                    }
                }
            }
        }
    }
}
