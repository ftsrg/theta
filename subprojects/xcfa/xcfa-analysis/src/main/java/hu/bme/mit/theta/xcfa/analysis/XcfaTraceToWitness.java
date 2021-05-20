package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.cfa.analysis.CfaTraceConcretizer;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static com.google.common.base.Preconditions.checkState;

public final class XcfaTraceToWitness {
	private static int stateCounter = 0;
	private static Trace<CfaState<ExplState>, CfaAction> concreteTrace;
	private static Graph witnessGraph;
	private XcfaTraceToWitness() {}

	public static Graph buildWitness(
			final Trace<CfaState<ExplState>, CfaAction> trace) {
		concreteTrace = trace;
		witnessGraph = new Graph("id", ""); // TODO what should the id be?

		addNodes();
		Map<Integer, String> explicitStates = collectExplicitStatesByStep();

		// add edges
		addEdges(explicitStates);
		return witnessGraph;
	}

	/**
	 * Adds edges to the witness graph based on the concrete trace and the explicit states
	 */
	private static void addEdges(Map<Integer, String> explicitStates) {
		for(int i = 0; i < concreteTrace.getActions().size(); i++) {
			Stmt actionStmt = concreteTrace.getAction(i).getStmts().get(0);
			StringBuilder edgeLabel = new StringBuilder();

			// add startline if there is a line number
			Integer lineNumber = getLineNumberMetadata(actionStmt, i);
			if (lineNumber != null) {
				edgeLabel.append("<data key=\"startline\">").append(lineNumber).append("</data>").append(System.lineSeparator());
			}

			if (actionStmt instanceof HavocStmt) {
				// we'll need the explicit states here
				// if we havoc a variable, but add it with a concrete value to the explicit state - that's an assumption
				String explicitState = explicitStates.get(i);
				String varName = ((HavocStmt<?>) concreteTrace.getAction(i).getStmts().get(0)).getVarDecl().getName(); // TODO lehet ures
				if (explicitState.contains(varName)) {
					// TODO this isn't the nicest way to handle a variable-value pair in an explicit state, but I couldn't find any better
					String varValue	= extractValueFromExplicitState(explicitState, varName);
					edgeLabel.append("<data key=\"assumption\">");
					edgeLabel.append(varName).append(" == ").append(varValue).append(";");
					edgeLabel.append("</data>").append(System.lineSeparator());
				}
			} // else if(actionStmt instanceof AssumeStmt) {}
			// TODO from AssumeStmts we can make control statements, if we add some additional annotations to the XCFA
			// TODO we might want to add AssigStmt-s as assumptions as well, although I need to check further example for that

			// not an official witness data key, so no validator will use it, but it helps readability
			edgeLabel.append("<data key=\"stmt\">").append(actionStmt.toString()).append("</data>");

			// label is done, add the edge to the witness graph
			addWitnessEdge(i, edgeLabel.toString());
		}
	}

	/**
	 * CFAs made from a C program with Theta were converted from an XCFA, which is able to hold the line number metadata
	 * if there is such a metadata, this function extracts is
	 * @param actionStmt statement we need the corresponging (C program) line number for
	 * @param index index of statement in the trace
	 * @return null, if no line number; the corrresponding line number otherwise
	 */
	private static Integer getLineNumberMetadata(Stmt actionStmt, int index) {
		// get line number, if there is one - it is in the form of XCFA metadata, in the CFAs corresponding XCFA
		boolean hasLineNumberMetadata = true;
		Integer lineNumber = null;

		Set<Object> xcfaEdge = XcfaMetadata.lookupMetadata("cfaEdge", concreteTrace.getAction(index).getEdges().get(0));
		if(xcfaEdge.isEmpty()) {
			hasLineNumberMetadata = false;
		}
		checkState(xcfaEdge.size() == 1, "A cfaEdge should only come from a single xcfaEdge");
		Object o = xcfaEdge.stream().findFirst().get();
		checkState(o instanceof XcfaEdge, "a cfaEdge metadata should only hold XcfaEdge types");
		Optional<Object> lNumber = XcfaMetadata.getMetadataValue(o, "lineNumber");
		if(lNumber.isEmpty()) {
			hasLineNumberMetadata = false;
		}

		if(hasLineNumberMetadata) {
			checkState(lNumber.get() instanceof Integer, "a lineNumber metadata should only hold integer types");
			lineNumber = (int) lNumber.get();
		}
		return lineNumber;
	}

	/**
	 * Adds a single node to the witness
	 *
	 * @param index index of state in trace
	 * @param label graphml label, e.g. <data key="entry">true</data>
	 */
	private static void addWitnessEdge(int index, String label) {
		witnessGraph.addEdge(concreteTrace.getState(index).getLoc().getName()+"_c"+index,
						concreteTrace.getState(index+1).getLoc().getName()+"_c"+(index+1),
							new EdgeAttributes.Builder().label(label).build()
							);
	}


	/**
	 * Adds a single node to the witness
	 *
	 * @param index index of state in trace
	 * @param label graphml label, e.g. <data key="entry">true</data>
	 */
	private static void addWitnessNode(int index, String label) {
		witnessGraph.addNode( concreteTrace.getState(index).getLoc().getName()+"_c"+index,
				new NodeAttributes.Builder().label(label).build()
		);
	}

	/**
	 * Adds nodes to the witness graph based on the concrete trace
	 */
	private static void addNodes() {
		// add entry state as a node
		addWitnessNode(0, "<data key=\"entry\">true</data>");

		// we'll use here, that the cex is a state-action-state-action... chain (that's why we can use an index as key)
		// (and that's the only way I could connect states and actions, as otherwise they are connected to locs/edges only)

		// add the other states as nodes (except the last one)
		for(int i = 1; i < concreteTrace.getStates().size()-1; i++) {
			addWitnessNode(i, "");
		}

		// add violation (end) state/node
		addWitnessNode(concreteTrace.getStates().size()-1, "<data key=\"violation\">true</data>");

	}

	/**
	 * Iterate through the states in the trace and put the explicit states of the states into a hashmap
	 * using the index of the state - 1 in the trace as a key (to associate it with the incoming edge/action)
	 *
	 * @return the resulting hashmap
	 */
	private static Map<Integer, String> collectExplicitStatesByStep() {
		Map<Integer, String> explStates = new HashMap<>();
		for(int i = 1; i < concreteTrace.getStates().size()-1; i++) {
			explStates.put(i - 1, concreteTrace.getState(i).getState().toString());
		}
		return explStates;
	}

	/**
	 * When finding an assumption, we need to extract the value of the variable from the explicit state
	 * @param explicitState the current explicit state in a string format
	 * @param varName the variable name we need the value of
	 * @return the value of varName in the explicit state
	 */
	private static String extractValueFromExplicitState(String explicitState, String varName) {
		String pattern = "(.*)\\("+varName+" (re)\\)(.*)";
		Pattern r = Pattern.compile(pattern);
		Matcher m = r.matcher(explicitState);
		if(m.find()) {
			return m.group(2);
		} else {
			return null;
		}
	}

}
