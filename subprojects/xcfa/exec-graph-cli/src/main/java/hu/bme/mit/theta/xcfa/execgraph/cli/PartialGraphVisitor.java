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

package hu.bme.mit.theta.xcfa.execgraph.cli;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.algorithm.mcm.analysis.CandidateExecutionGraph;
import hu.bme.mit.theta.common.Tuple;
import hu.bme.mit.theta.common.Tuple1;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.exec.graph.cli.dsl.gen.GraphBaseVisitor;
import hu.bme.mit.theta.exec.graph.cli.dsl.gen.GraphLexer;
import hu.bme.mit.theta.exec.graph.cli.dsl.gen.GraphParser;
import hu.bme.mit.theta.graphsolver.ThreeVL;
import kotlin.Pair;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;

public class PartialGraphVisitor extends GraphBaseVisitor<Void> {
    private final Map<String, Integer> events = new LinkedHashMap<>();
    private final Set<String> relations = new LinkedHashSet<>();
    private final Set<String> sets = new LinkedHashSet<>();
    private final Set<Pair<String, Tuple>> positiveFacts = new LinkedHashSet<>();

    @Override
    public Void visitNode(GraphParser.NodeContext ctx) {
        var id = Integer.parseInt(ctx.eventID().getText());
        Preconditions.checkState(!events.containsValue(id), "Already existing event IDs cannot be added.");
        events.put(ctx.name.getText(), id);
        if (ctx.labels() != null) {
            for (GraphParser.LabelContext labelContext : ctx.labels().label()) {
                var label = labelContext.ID().getText();
                sets.add(label);
                positiveFacts.add(new Pair<>(label, Tuple1.of(id)));
            }
        }
        return null;
    }

    @Override
    public Void visitRelation(GraphParser.RelationContext ctx) {
        var fromId = events.get(ctx.source.getText());
        checkNotNull(fromId, "Source event not known for " + ctx.getText());
        var toId = events.get(ctx.target.getText());
        checkNotNull(toId, "Taret event not known for " + ctx.getText());

        var label = ctx.label().getText();
        relations.add(label);
        positiveFacts.add(new Pair<>(label, Tuple2.of(fromId, toId)));
        return null;
    }

    public static CandidateExecutionGraph getPartialGraph(final File file) throws IOException {
        FileInputStream inputStream = new FileInputStream(file);
        final CharStream input = CharStreams.fromStream(inputStream);

        final GraphLexer lexer = new GraphLexer(input);
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        final GraphParser parser = new GraphParser(tokens);
        inputStream.close();

        var partialGraphVisitor = new PartialGraphVisitor();
        parser.graph().accept(partialGraphVisitor);
        Map<Pair<String, Tuple>, ThreeVL> facts = new LinkedHashMap<>();
        var eventList = partialGraphVisitor.events.values().stream().toList();
        for (Integer a : eventList) {
            for (String set : partialGraphVisitor.sets) {
                if (partialGraphVisitor.positiveFacts.contains(new Pair<>(set, Tuple1.of(a)))) {
                    facts.put(new Pair<>(set, Tuple1.of(a)), ThreeVL.TRUE);
                } else {
                    facts.put(new Pair<>(set, Tuple1.of(a)), ThreeVL.FALSE);
                }
            }
            for (Integer b : eventList) {
                for (String relation : partialGraphVisitor.relations) {
                    if (partialGraphVisitor.positiveFacts.contains(new Pair<>(relation, Tuple2.of(a, b)))) {
                        facts.put(new Pair<>(relation, Tuple2.of(a, b)), ThreeVL.TRUE);
                    } else {
                        facts.put(new Pair<>(relation, Tuple2.of(a, b)), ThreeVL.FALSE);
                    }
                }
            }
        }
        return new CandidateExecutionGraph(partialGraphVisitor.events.values().stream().toList(), facts);
    }
}
