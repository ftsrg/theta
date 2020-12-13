package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;
import hu.bme.mit.theta.common.datalog.DatalogArgument;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

public final class ExecutionGraphDatabase extends Datalog {
    private final Relation nodeLabels;
    private final Relation edgeLabels;
    private final Relation fixNodes;
    private final Relation finalNodes;
    private final Relation threadMapping;
    private final Relation varMapping;
    private final Map<String, Relation> patterns;

    private ExecutionGraphDatabase() {
        this.nodeLabels = createRelation(2);
        this.edgeLabels = createRelation(3);
        this.fixNodes = createRelation(1);
        this.finalNodes = createRelation(1);
        this.threadMapping = createRelation(2);
        this.varMapping = createRelation(2);
        this.patterns = new LinkedHashMap<>();

        Variable finalVar, predecessorVar;
        this.finalNodes.addRule( // finalRead and finalWrite!!
                TupleN.of(finalVar = getVariable()),
                Set.of(
                        Tuple2.of(
                                this.fixNodes,
                                TupleN.of(finalVar)
                        ),
                        Tuple2.of(
                                this.finalNodes,
                                TupleN.of(predecessorVar = getVariable())
                        ),
                        Tuple2.of(
                                this.edgeLabels,
                                TupleN.of(predecessorVar, finalVar, getVariable())
                        )
                )
        );
    }

    public static ExecutionGraphDatabase createExecutionGraph() {
        return new ExecutionGraphDatabase();
    }

    public Relation addPattern(String name, TupleN<Variable> args, Set<Tuple2<Relation, TupleN<Variable>>> dependencies) {
        checkState(!this.patterns.containsKey(name), "Pattern " + name + " already exists in the database");
        Relation relation;
        this.patterns.put(name, relation = createRelation(4));
        relation.addRule(args, dependencies);
        return relation;
    }

    public Optional<Relation> getPattern(String name) {
        return Optional.ofNullable(patterns.get(name));
    }


    public Relation getNodeLabels() {
        return nodeLabels;
    }

    public Relation getEdgeLabels() {
        return edgeLabels;
    }

    public Relation getVolatileNodes() {
        return volatileNodes;
    }

    public Relation getThreadMapping() {
        return threadMapping;
    }

    public Relation getVarMapping() {
        return varMapping;
    }

    public Relation getRevisitables() {
        return revisitables;
    }
}
