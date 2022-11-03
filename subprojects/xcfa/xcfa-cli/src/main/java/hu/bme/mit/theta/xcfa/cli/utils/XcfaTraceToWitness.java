/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.cli.utils;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.c2xcfa.CMetaData;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.ChoiceType;
import hu.bme.mit.theta.xcfa.model.SequenceLabel;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static hu.bme.mit.theta.c2xcfa.CMetaDataKt.getCMetaData;

public final class XcfaTraceToWitness {
    private static Trace<XcfaState<ExplState>, XcfaAction> concreteTrace;
    private static Graph witnessGraph;
    private static Integer nodeCounter = 0;

    private XcfaTraceToWitness() {
    }

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

        for (int i = 0; i < concreteTrace.getActions().size(); i++) {
            List<XcfaLabel> labelList = ((SequenceLabel)concreteTrace.getAction(i).getLabel()).getLabels();
            List<String> edgesFromAction = new ArrayList<>();
            for (XcfaLabel label : labelList) {
                Optional<String> optionalLabel = makeEdgeLabelFromStatement(label, concreteTrace.getState(i + 1).getSGlobal().getVal());
                optionalLabel.ifPresent(edgesFromAction::add);
            }

            if (concreteTrace.getAction(i).getTarget().getError() && edgesFromAction.size() == 0) {
                addViolationNode();
                addWitnessEdge("");
            }
            // otherwise:
            for (int j = 0; j < edgesFromAction.size(); j++) {
                // if it is the last edge before reaching the violation node
                if (concreteTrace.getAction(i).getTarget().getError() && j + 1 == edgesFromAction.size()) {
                    addViolationNode();
                } else { // else the next node should be a normal one
                    addNextWitnessNode("");
                }
                // label is done, add the edge to the witness graph
                addWitnessEdge(edgesFromAction.get(j));
            }
        }

    }

    private static Optional<String> makeEdgeLabelFromStatement(XcfaLabel label, Valuation nextVal) {
        if (!(label instanceof StmtLabel) || !(((StmtLabel) label).getStmt() instanceof HavocStmt || ((StmtLabel) label).getStmt() instanceof AssumeStmt)) {
            return Optional.empty();
        }

        Optional<CMetaData> metadataOpt = Optional.ofNullable(getCMetaData(label));

        if (metadataOpt.isEmpty()) {
            return Optional.empty();
        }

        CMetaData metaData = metadataOpt.get();

        StringBuilder edgeLabel = new StringBuilder();

        if (metaData.getLineNumberStart() != -1) {
            edgeLabel.append("<data key=\"startline\">").append(metaData.getLineNumberStart()).append("</data>").append(System.lineSeparator());
        }

        if (metaData.getLineNumberStop() != -1) {
            edgeLabel.append("<data key=\"endline\">").append(metaData.getLineNumberStop()).append("</data>").append(System.lineSeparator());
        }

        if (metaData.getOffsetStart() != -1) {
            edgeLabel.append("<data key=\"startoffset\">").append(metaData.getOffsetStart()).append("</data>").append(System.lineSeparator());
        }

        if (((StmtLabel) label).getStmt() instanceof HavocStmt) {
            Optional<? extends LitExpr<?>> value = nextVal.eval(((HavocStmt<?>) ((StmtLabel) label).getStmt()).getVarDecl());
            String varName = ((HavocStmt<?>) ((StmtLabel) label).getStmt()).getVarDecl().getName();
            if (value.isPresent()) {
                edgeLabel.append("<data key=\"assumption\">");
                edgeLabel.append(varName).append(" == ").append(printLit(value.get())).append(";");
                edgeLabel.append("</data>").append(System.lineSeparator());
            }
        } else if (((StmtLabel) label).getStmt() instanceof AssumeStmt) {
            if (((StmtLabel) label).getChoiceType() == ChoiceType.ALTERNATIVE_PATH) {
                edgeLabel.append("<data key=\"control\">condition-").append("false").append("</data>").append(System.lineSeparator());
            } else if (((StmtLabel) label).getChoiceType() == ChoiceType.MAIN_PATH) {
                edgeLabel.append("<data key=\"control\">condition-").append("true").append("</data>").append(System.lineSeparator());
            }
        }
        // not an official witness data key, so no validator will use it, but it helps readability
        edgeLabel.append("<data key=\"stmt\">").append(escapeXml(label.toString())).append("</data>").append(System.lineSeparator());
        edgeLabel.append("<data key=\"source\">").append(escapeXml(metaData.getSourceText())).append("</data>");
        return Optional.of(edgeLabel.toString());
    }

    private static String printLit(final LitExpr<?> litExpr) {
        if (litExpr instanceof BvLitExpr) {
            final boolean[] value = ((BvLitExpr) litExpr).getValue();
            BigInteger intValue = BigInteger.ZERO;
            for (int i = 0; i < value.length; i++) {
                boolean b = value[i];
                if (b) {
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
                if (i % 4 == 0 && i > 0) {
                    if (aggregate < 10) hexDigits.add((char) ('0' + aggregate));
                    else hexDigits.add((char) ('A' - 10 + aggregate));
                    aggregate = 0;
                }
                if (boolList.get(i)) aggregate += 1 << (i % 4);
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
        witnessGraph.addEdge("N" + (nodeCounter - 2),
                "N" + (nodeCounter - 1),
                new EdgeAttributes.Builder().label(label).build()
        );
    }

    /**
     * Adds the next node to the witness
     *
     * @param label graphml label, e.g. <data key="entry">true</data>, might be empty
     */
    private static void addNextWitnessNode(String label) {
        witnessGraph.addNode("N" + nodeCounter.toString(),
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