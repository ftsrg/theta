package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

public final class XcfaTraceToWitness {
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
			Integer startLineNumber = getEdgeMetadata(concreteTrace.getAction(i).getEdges().get(0), "lineNumberStart");
			if (startLineNumber != -1) {
				edgeLabel.append("<data key=\"startline\">").append(startLineNumber).append("</data>").append(System.lineSeparator());
			}

			// add endline if there is a line number
			Integer endLineNumber = getEdgeMetadata(concreteTrace.getAction(i).getEdges().get(0), "lineNumberStop");
			if (endLineNumber != -1) {
				edgeLabel.append("<data key=\"endline\">").append(endLineNumber).append("</data>").append(System.lineSeparator());
			}

			// add offset if there is an offset start
			Integer offsetStartNumber = getEdgeMetadata(concreteTrace.getAction(i).getEdges().get(0), "offsetStart");
			if (offsetStartNumber != -1) {
				edgeLabel.append("<data key=\"offset\">").append(offsetStartNumber).append("</data>").append(System.lineSeparator());
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
			} else if (actionStmt instanceof AssumeStmt) {
				// when we need assumptions (by controlflow branches), the outer = means a cond true a /= means a cond false
				boolean conditionTrue;
				if(((AssumeStmt) actionStmt).getCond() instanceof EqExpr) {
					conditionTrue = true;
				} else if (((AssumeStmt) actionStmt).getCond() instanceof NeqExpr) {
					conditionTrue = false;
				} else {
					throw new RuntimeException("Assume statement condition should either be an Eq or a Neq Expr");
				}

				edgeLabel.append("<data key=\"control\">condition-").append(conditionTrue?"true":"false").append("</data>");
			}

			// not an official witness data key, so no validator will use it, but it helps readability
			edgeLabel.append("<data key=\"stmt\">").append(actionStmt.toString()).append("</data>");

			// label is done, add the edge to the witness graph
			addWitnessEdge(i, edgeLabel.toString());
		}
	}

	/**
	 * CFAs made from a C program with Theta were converted from an XCFA, which is able to hold the line number metadata
	 * if there is such a metadata, this function extracts is
	 * @param edge the edge we need the line number for
	 * @return null, if no line number; the corrresponding line number otherwise
	 */
	private static int getEdgeMetadata(CFA.Edge edge, String key) {
		Set<Object> xcfaEdges = XcfaMetadata.lookupMetadata("cfaEdge", edge);
		for (Object xcfaEdge : xcfaEdges) {
			Object sourceStatement = XcfaMetadata.lookupMetadata(xcfaEdge).get("sourceStatement");
			if(sourceStatement != null) {
				Object metadataNumber = XcfaMetadata.lookupMetadata(sourceStatement).get(key);
				if(metadataNumber instanceof Integer) {
					return (int) metadataNumber;
				}
			}
		}
		return -1;
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
		StringBuilder entryLabel = new StringBuilder();
		entryLabel.append("<data key=\"entry\">true</data>").append(System.lineSeparator());
		// entryLabel.append("<data key=\"expl-state\">").append(concreteTrace.getState(0)
		//		.getState().toString()).append("</data>").append(System.lineSeparator());
		// add entry state as a node
		addWitnessNode(0, entryLabel.toString());

		// we'll use here, that the cex is a state-action-state-action... chain (that's why we can use an index as key)
		// (and that's the only way I could connect states and actions, as otherwise they are connected to locs/edges only)

		// add the other states as nodes (except the last one)
		for(int i = 1; i < concreteTrace.getStates().size()-1; i++) {
			StringBuilder nodeLabel = new StringBuilder();
		//	nodeLabel.append("<data key=\"expl-state\">").append(concreteTrace.getState(i)
		//			.getState().toString()).append("</data>").append(System.lineSeparator());
			addWitnessNode(i, nodeLabel.toString());
		}

		StringBuilder endLabel = new StringBuilder();
		endLabel.append("<data key=\"violation\">true</data>").append(System.lineSeparator());
		// endLabel.append("<data key=\"expl-state\">").append(concreteTrace.getState(concreteTrace.getStates().size()-1)
		//		.getState().toString()).append("</data>").append(System.lineSeparator());
		// add violation (end) state/node
		addWitnessNode(concreteTrace.getStates().size()-1, endLabel.toString());
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
		explicitState = explicitState.replaceFirst("\\(ExplState ", "");
		explicitState = explicitState.substring(0, explicitState.length() - 1);
		String[] pairs = explicitState.split("\n");
		String value = null;
		for (String pair : pairs) {
			if(pair.contains("("+varName)) {
				value = pair.replaceFirst("\\s*\\(", "(");
				value = value.replaceFirst("\\("+varName+" ", "");
				value = value.substring(0, value.length()-1);
			}
		}
		return value;
	}

}
