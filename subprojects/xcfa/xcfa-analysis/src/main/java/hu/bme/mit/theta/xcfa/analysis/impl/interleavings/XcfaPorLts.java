package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import hu.bme.mit.theta.analysis.algorithm.PorLts;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class XcfaPorLts extends PorLts<XcfaState<?>, XcfaAction> {

	private final XcfaLts simpleXcfaLts;

	private final Random random = new Random();

	public XcfaPorLts(XCFA xcfa) {
		simpleXcfaLts = new XcfaLts(xcfa);
		globalVars = xcfa.getGlobalVars();
		collectBackwardEdges(xcfa);
	}

	@Override
	protected Collection<XcfaAction> getAllEnabledActionsFor(XcfaState<?> state) {
		return simpleXcfaLts.getEnabledActionsFor(state);
	}

	@Override
	protected Collection<XcfaAction> getPersistentSetFirstActions(Collection<XcfaAction> allEnabledActions) {
		var enabledActionsByProcess = allEnabledActions.stream().collect(Collectors.groupingBy(XcfaAction::getProcess));
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
	protected boolean areDependents(XcfaAction persistentSetAction, XcfaAction action) {
		return persistentSetAction.getProcess().equals(action.getProcess()) ||
				getInfluencedGlobalVars(action.getEdge()).stream().anyMatch(varDecl ->
						getUsedGlobalVars(persistentSetAction.getEdge()).contains(varDecl));
	}

	@Override
	protected boolean isBackwardAction(XcfaAction action) {
		return backwardEdges.contains(action.getEdge());
	}

	/**
	 * Global variables in the XCFA.
	 */
	private final List<VarDecl<? extends Type>> globalVars;

	/**
	 * Global variables used by an edge.
	 */
	private final HashMap<XcfaEdge, Set<VarDecl<? extends Type>>> usedGlobalVars = new HashMap<>();

	/**
	 * Global variables that are used by the key edge or by edges reachable from the current state via a given edge.
	 */
	private final HashMap<XcfaEdge, Set<VarDecl<? extends Type>>> influencedGlobalVars = new HashMap<>();

	/**
	 * Returns the global variables that an edge uses (it is present in one of its labels).
	 *
	 * @param edge whose global variables are to be returned
	 * @return the set of used global variables
	 */
	private Set<VarDecl<? extends Type>> getDirectlyUsedGlobalVars(XcfaEdge edge) {
		Set<VarDecl<?>> vars = new HashSet<>();
		edge.getLabels().forEach(label -> LabelUtils.getVars(label).forEach(usedVar -> {
			if (globalVars.contains(usedVar)) {
				vars.add(usedVar);
			}
		}));
		return vars;
	}

	/**
	 * Returns the global variables that an edge uses or if it is the start of an atomic block the global variables
	 * that are used in the atomic block.
	 *
	 * @param edge whose global variables are to be returned
	 * @return the set of directly or indirectly used global variables
	 */
	private Set<VarDecl<? extends Type>> getUsedGlobalVars(XcfaEdge edge) {
		if (!usedGlobalVars.containsKey(edge)) {
			Set<VarDecl<?>> vars;
			var labels = edge.getLabels();
			if (labels.stream().anyMatch(label -> label instanceof XcfaLabel.AtomicBeginXcfaLabel)) {
				vars = getGlobalVarsWithBFS(edge, xcfaEdge -> xcfaEdge.getLabels().stream().noneMatch(label -> label instanceof XcfaLabel.AtomicEndXcfaLabel));
			} else {
				vars = getDirectlyUsedGlobalVars(edge);
			}
			usedGlobalVars.put(edge, vars);
		}
		return usedGlobalVars.get(edge);
	}

	/**
	 * Returns the global variables used by the given edge or by edges that are reachable via the given edge
	 * ("influenced global variables").
	 *
	 * @param edge whose successor edges' global variables are to be returned.
	 * @return the set of influenced global variables
	 */
	private Set<VarDecl<? extends Type>> getInfluencedGlobalVars(XcfaEdge edge) {
		if (!influencedGlobalVars.containsKey(edge)) {
			influencedGlobalVars.put(edge, getGlobalVarsWithBFS(edge, xcfaEdge -> true));
		}
		return influencedGlobalVars.get(edge);
	}

	/**
	 * Returns global variables encountered in a search starting from a given edge.
	 *
	 * @param startEdge the start point (edge) of the search
	 * @param visitEdge the predicate that tells whether an edge has to be explored
	 * @return the set of encountered global variables
	 */
	private Set<VarDecl<?>> getGlobalVarsWithBFS(XcfaEdge startEdge, Predicate<XcfaEdge> visitEdge) {
		Set<VarDecl<?>> vars = new HashSet<>();
		List<XcfaEdge> exploredEdges = new ArrayList<>();
		List<XcfaEdge> edgesToExplore = new ArrayList<>();
		edgesToExplore.add(startEdge);

		while (!edgesToExplore.isEmpty()) {
			var exploring = edgesToExplore.remove(0);
			vars.addAll(getDirectlyUsedGlobalVars(exploring));

			var outgoingEdges = new ArrayList<>(exploring.getTarget().getOutgoingEdges());
			List<XcfaLabel.StartThreadXcfaLabel> startThreads = exploring.getLabels().stream()
					.filter(label -> label instanceof XcfaLabel.StartThreadXcfaLabel)
					.map(label -> (XcfaLabel.StartThreadXcfaLabel) label).collect(Collectors.toList());
			if (startThreads.size() > 0) { // for start thread labels, the thread procedure must be explored, too!
				startThreads.forEach(startThread ->
						outgoingEdges.addAll(startThread.getProcess().getMainProcedure().getInitLoc().getOutgoingEdges()));
			}

			for (var newEdge : outgoingEdges) {
				if (!exploredEdges.contains(newEdge) && visitEdge.test(newEdge)) {
					edgesToExplore.add(newEdge);
				}
			}
			exploredEdges.add(exploring);
		}
		return vars;
	}


	/**
	 * Backward edges in the XCFA (an edge of a loop).
	 */
	private final Set<XcfaEdge> backwardEdges = new HashSet<>();

	/**
	 * Collects backward edges of the given XCFA.
	 *
	 * @param xcfa the XCFA whose backward edges are to be collected
	 */
	private void collectBackwardEdges(XCFA xcfa) {
		for (var process : xcfa.getProcesses()) {
			for (var procedure : process.getProcedures()) {
				// DFS for every procedure of the XCFA to discover backward edges
				Set<XcfaLocation> visitedLocations = new HashSet<>();
				Stack<XcfaLocation> stack = new Stack<>();

				stack.push(procedure.getInitLoc()); // start from the initial location of the procedure
				while (!stack.isEmpty()) {
					XcfaLocation visiting = stack.pop();
					visitedLocations.add(visiting);
					for (var outgoingEdge : visiting.getOutgoingEdges()) {
						var target = outgoingEdge.getTarget();
						if (visitedLocations.contains(target)) { // backward edge
							backwardEdges.add(outgoingEdge);
						} else {
							stack.push(target);
						}
					}
				}
			}
		}
	}
}
