package hu.bme.mit.theta.xcfa.analysis.common;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.frontend.FrontendMetadata;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

public final class XcfaTraceToWitness {
	private static Trace<XcfaState<ExplState>, XcfaAction> concreteTrace;
	private static Graph witnessGraph;
	private static Integer nodeCounter = 0;

	private XcfaTraceToWitness() {}

	public static Graph buildWitness(
			final Trace<XcfaState<ExplState>, XcfaAction> trace) {
		concreteTrace = trace;
		witnessGraph = new Graph("id", ""); // TODO what should the id be?

		// add edges
		addEdges();
		return witnessGraph;
	}

	/**
	 * Adds edges to the witness graph based on the concrete trace and the explicit states
	 */
	private static void addEdges() {
		addEntryNode();

		for(int i = 0; i < concreteTrace.getActions().size(); i++) {
			List<Stmt> stmtList = concreteTrace.getAction(i).getStmts();
			List<String> edgesFromAction = new ArrayList<>();
			for (Stmt stmt : stmtList) {
				Optional<String> optionalLabel = makeEdgeLabelFromStatement(stmt, concreteTrace.getState(i+1).getGlobalState().getVal());
				optionalLabel.ifPresent(edgesFromAction::add);
			}

			if(concreteTrace.getAction(i).getTarget().isErrorLoc() && edgesFromAction.size() == 0) {
				addViolationNode();
				addWitnessEdge("");
			}
			// otherwise:
			for (int j = 0; j < edgesFromAction.size(); j++) {
				// if it is the last edge before reaching the violation node
				if (concreteTrace.getAction(i).getTarget().isErrorLoc() && j + 1 == edgesFromAction.size()) {
					addViolationNode();
				} else { // else the next node should be a normal one
					addNextWitnessNode("");
				}
				// label is done, add the edge to the witness graph
				addWitnessEdge(edgesFromAction.get(j));
			}
		}

	}

	private static Optional<String> makeEdgeLabelFromStatement(Stmt stmt, Valuation nextVal) {
		if(!(stmt instanceof HavocStmt || stmt instanceof AssumeStmt)) {
			return Optional.empty();
		}

		final Optional<Object> sourceStatement = FrontendMetadata.getMetadataValue(stmt, "sourceStatement");
		if(sourceStatement.isEmpty()) {
			return Optional.empty();
		}

		Map<String, ?> metadata = FrontendMetadata.lookupMetadata(sourceStatement.get());
		StringBuilder edgeLabel = new StringBuilder();

		Object lineNumberStartO = metadata.get("lineNumberStart");
		if(lineNumberStartO instanceof Integer) {
			Integer startLineNumber = (Integer)lineNumberStartO;
			if (startLineNumber != -1) {
				edgeLabel.append("<data key=\"startline\">").append(startLineNumber).append("</data>").append(System.lineSeparator());
			}
		}

		Object lineNumberStopO = metadata.get("lineNumberStop");
		if(lineNumberStartO instanceof Integer) {
			Integer endLineNumber = (Integer)lineNumberStopO;
			if (endLineNumber != -1) {
				edgeLabel.append("<data key=\"endline\">").append(endLineNumber).append("</data>").append(System.lineSeparator());
			}
		}

		Object offsetStartO = metadata.get("offsetStart");
		if(offsetStartO instanceof Integer) {
			Integer offsetStartNumber = (Integer)offsetStartO;
			if (offsetStartNumber != -1) {
				edgeLabel.append("<data key=\"startoffset\">").append(offsetStartNumber).append("</data>").append(System.lineSeparator());
			}
		}

		if (stmt instanceof HavocStmt) {
			Optional<? extends LitExpr<?>> value = nextVal.eval(((HavocStmt<?>) stmt).getVarDecl());
			Object varName = ((HavocStmt<?>) stmt).getVarDecl().getName();
			if(value.isPresent() && FrontendMetadata.getMetadataValue(stmt, "sourceStatement").isPresent()) {
				edgeLabel.append("<data key=\"assumption\">");
				edgeLabel.append(varName).append(" == ").append(printLit(value.get())).append(";");
				edgeLabel.append("</data>").append(System.lineSeparator());
			}
		} else if (stmt instanceof AssumeStmt) {
			if(((AssumeStmt) stmt).getCond() instanceof EqExpr) {
				edgeLabel.append("<data key=\"control\">condition-").append("false").append("</data>").append(System.lineSeparator());
			} else if (((AssumeStmt) stmt).getCond() instanceof NeqExpr) {
				edgeLabel.append("<data key=\"control\">condition-").append("true").append("</data>").append(System.lineSeparator());
			}
		}
		// not an official witness data key, so no validator will use it, but it helps readability
		edgeLabel.append("<data key=\"stmt\">").append(escapeXml(stmt.toString())).append("</data>");
		return Optional.of(edgeLabel.toString());
	}

	private static String printLit(final LitExpr<?> litExpr) {
		if(litExpr instanceof BvLitExpr) {
			final boolean[] value = ((BvLitExpr) litExpr).getValue();
			BigInteger intValue = BigInteger.ZERO;
			for (int i = 0; i < value.length; i++) {
				boolean b = value[i];
				if(b) {
					intValue = intValue.add(BigInteger.ONE.shiftLeft(value.length - 1 - i));
				}
			}
			return "0x" + intValue.toString(16);
		} else if (litExpr instanceof FpLitExpr) {
			List<Boolean> boolList = new ArrayList<>();
			List<Boolean> tmpList = new ArrayList<>();
			for (boolean b : ((FpLitExpr) litExpr).getSignificand().getValue()) {
				tmpList.add(b);
			}
			boolList.addAll(Lists.reverse(tmpList));
			tmpList.clear();
			for (boolean b : ((FpLitExpr) litExpr).getExponent().getValue()) {
				tmpList.add(b);
			}
			boolList.addAll(Lists.reverse(tmpList));
			boolList.add(((FpLitExpr) litExpr).getHidden());
			int aggregate = 0;
			List<Character> hexDigits = new ArrayList<>();
			for (int i = 0; i < boolList.size(); i++) {
				if(i % 4 == 0 && i > 0) {
					if(aggregate < 10) hexDigits.add((char) ('0' + aggregate));
					else hexDigits.add((char) ('A' - 10 + aggregate));
					aggregate = 0;
				}
				if(boolList.get(i)) aggregate+=1 << (i % 4);
			}
			if (aggregate < 10) hexDigits.add((char) ('0' + aggregate));
			else hexDigits.add((char) ('A' - 10 + aggregate));

			StringBuilder stringBuilder = new StringBuilder("0x");
			for (Character character : Lists.reverse(hexDigits)) {
				stringBuilder.append(character);
			}
			return stringBuilder.toString();
		} else {
			return litExpr.toString();
		}
	}

	private static String escapeXml(String toEscape) {
		toEscape = toEscape.replace("\"", "&quot;");
		toEscape = toEscape.replace("'", "&apos;");
		toEscape = toEscape.replace("<", "&lt;");
		toEscape = toEscape.replace(">", "&gt;");
		toEscape = toEscape.replace("&", "&amp;");
		return toEscape;
	}

	/**
	 * Adds the next witness edge (edge between the last two added nodes)
	 *
	 * @param label graphml label, e.g. <data key="startline">12</data>...
	 */
	private static void addWitnessEdge(String label) {
		witnessGraph.addEdge("N"+(nodeCounter - 2),
				"N"+(nodeCounter-1),
				new EdgeAttributes.Builder().label(label).build()
		);
	}

	/**
	 * Adds the next node to the witness
	 *
	 * @param label graphml label, e.g. <data key="entry">true</data>, might be empty
	 */
	private static void addNextWitnessNode(String label) {
		witnessGraph.addNode( "N"+nodeCounter.toString(),
				new NodeAttributes.Builder().label(label).build()
		);
		nodeCounter++;
	}

	private static void addEntryNode() {
		StringBuilder entryLabel = new StringBuilder();
		entryLabel.append("<data key=\"entry\">true</data>").append(System.lineSeparator());
		// add entry state as a node
		addNextWitnessNode(entryLabel.toString());
	}

	private static void addViolationNode() {
		StringBuilder endLabel = new StringBuilder();
		endLabel.append("<data key=\"violation\">true</data>").append(System.lineSeparator());
		// add violation (end) state/node
		addNextWitnessNode(endLabel.toString());
	}
}
