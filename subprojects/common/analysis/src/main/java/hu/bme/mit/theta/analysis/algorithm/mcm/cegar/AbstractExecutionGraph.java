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

package hu.bme.mit.theta.analysis.algorithm.mcm.cegar;

import com.google.common.collect.Sets;
import hu.bme.mit.theta.analysis.algorithm.mcm.EncodedRelationWrapper;
import hu.bme.mit.theta.analysis.algorithm.mcm.EventConstantLookup;
import hu.bme.mit.theta.analysis.algorithm.mcm.MCM;
import hu.bme.mit.theta.analysis.algorithm.mcm.MCMConstraint;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.GenericDatalogArgument;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import tools.refinery.store.map.Cursor;
import tools.refinery.store.model.Model;
import tools.refinery.store.model.ModelStore;
import tools.refinery.store.model.ModelStoreImpl;
import tools.refinery.store.model.Tuple;
import tools.refinery.store.model.representation.DataRepresentation;
import tools.refinery.store.model.representation.Relation;
import tools.refinery.store.model.representation.TruthValue;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public class AbstractExecutionGraph {
    private final Map<String, Relation<TruthValue>> preDefinedRelations = Map.ofEntries(
            Map.entry("emptyset", new Relation<>("emptyset", 1, TruthValue.FALSE)),
            Map.entry("W", new Relation<>("W", 1, TruthValue.FALSE)),
            Map.entry("R", new Relation<>("R", 1, TruthValue.FALSE)),
            Map.entry("M", new Relation<>("M", 1, TruthValue.FALSE)),
            Map.entry("IW", new Relation<>("IW", 1, TruthValue.FALSE)),
            Map.entry("FW", new Relation<>("FW", 1, TruthValue.FALSE)),
            Map.entry("B", new Relation<>("B", 1, TruthValue.FALSE)),
            Map.entry("RMW", new Relation<>("RMW", 1, TruthValue.FALSE)),
            Map.entry("F", new Relation<>("F", 1, TruthValue.FALSE)),

            Map.entry("U", new Relation<>("U", 1, TruthValue.FALSE)),
            Map.entry("T", new Relation<>("T", 1, TruthValue.UNKNOWN)),

            Map.entry("po", new Relation<>("po", 2, TruthValue.FALSE)),
            Map.entry("po-raw", new Relation<>("po-raw", 2, TruthValue.FALSE)),
            Map.entry("addr", new Relation<>("addr", 2, TruthValue.FALSE)),
            Map.entry("data", new Relation<>("data", 2, TruthValue.FALSE)),
            Map.entry("ctrl", new Relation<>("ctrl", 2, TruthValue.FALSE)),
            Map.entry("rmw", new Relation<>("rmw", 2, TruthValue.FALSE)),
            Map.entry("amo", new Relation<>("amo", 2, TruthValue.FALSE)),

            Map.entry("id", new Relation<>("id", 2, TruthValue.FALSE)),
            Map.entry("loc-raw", new Relation<>("loc-raw", 2, TruthValue.FALSE)),
            Map.entry("loc", new Relation<>("loc", 2, TruthValue.FALSE)),
//            Map.entry("ext", new Relation<>("ext", 2, TruthValue.FALSE)),
            Map.entry("int-raw", new Relation<>("int-raw", 2, TruthValue.FALSE)),
            Map.entry("int", new Relation<>("int", 2, TruthValue.FALSE)),

            Map.entry("rf", new Relation<>("rf", 2, TruthValue.UNKNOWN)),
            Map.entry("co", new Relation<>("co", 2, TruthValue.UNKNOWN))
    );
    private final Map<String, Relation<TruthValue>> tags;
    private final MCM mcm;
    private final ModelStore modelStore;
    private Model currentModel;
    private final EncodedRelationWrapper encodedRelationWrapper;
    private int lastCnt = 1;

    public AbstractExecutionGraph(final Collection<String> tags, final Solver solver, final MCM mcm) {
        this.mcm = mcm;
        this.tags = new LinkedHashMap<>();
        tags.forEach(t -> this.tags.put(t, new Relation<>(t, 1, TruthValue.FALSE)));
        modelStore = new ModelStoreImpl(Sets.union(Set.copyOf(this.tags.values()), Set.copyOf(preDefinedRelations.values())));
        currentModel = modelStore.createModel();
        encodedRelationWrapper = new EncodedRelationWrapper(solver);
    }

    // Encoder method

    public EventConstantLookup encode() {
        updateCalculatedRelations(); // this won't be necessary when Refinery will support derivation rules

        final List<Integer> idList = getMustValues(rel("U")).stream().map(this::unbox).collect(Collectors.toList());

        for (final MCMConstraint constraint : mcm.getConstraints()) {
            constraint.encodeEvents(idList, encodedRelationWrapper);
        }

        final Collection<Relation<TruthValue>> binaryRelations = preDefinedRelations.values().stream().filter(r -> r.getArity() == 2).toList();
        final Collection<Relation<TruthValue>> unaryRelations = Sets.union(Set.copyOf(tags.values()), preDefinedRelations.values().stream().filter(r -> r.getArity() == 1).collect(Collectors.toSet()));

        for (final int i : idList) {
            for (final Relation<TruthValue> unaryRelation : unaryRelations) {
                TruthValue truthValue = currentModel.get(unaryRelation, Tuple.of(i));
                if(truthValue.must()) {
                    encodedRelationWrapper.getSolver().add(getOrCreate(encodedRelationWrapper, idList, unaryRelation.getName(), true).get(TupleN.of(i)).getRef());
                } else if(!truthValue.may()) {
                    encodedRelationWrapper.getSolver().add(Not(getOrCreate(encodedRelationWrapper, idList, unaryRelation.getName(), true).get(TupleN.of(i)).getRef()));
                }
            }
            for (final int j : idList) {
                for (final Relation<TruthValue> binaryRelation : binaryRelations) {
                    TruthValue truthValue = currentModel.get(binaryRelation, Tuple.of(i, j));
                    if(truthValue.must()) {
                        encodedRelationWrapper.getSolver().add(getOrCreate(encodedRelationWrapper, idList, binaryRelation.getName(), false).get(TupleN.of(i, j)).getRef());
                    } else if(!truthValue.may()) {
                        encodedRelationWrapper.getSolver().add(Not(getOrCreate(encodedRelationWrapper, idList, binaryRelation.getName(), false).get(TupleN.of(i, j)).getRef()));
                    }
                }
            }
        }

        // special encoding is necessary to ensure a maximal set of events are in-trace:
        EventConstantLookup t = getOrCreate(encodedRelationWrapper, idList, "T", true);
        for (final int i : idList) {
            List<List<Integer>> partitions = new ArrayList<>();
            if(currentModel.get(rel("IW"), Tuple.of(i)).must()) encodedRelationWrapper.getSolver().add(t.get(TupleN.of(i)).getRef());

            for (final int j : idList) {
                if(currentModel.get(rel("po"), Tuple.of(i, j)).must()) {
                    boolean found = false;
                    for (List<Integer> partition : partitions) {
                        if(currentModel.get(rel("int"), Tuple.of(partition.get(0), j)).must()) {
                            found = true;
                            partition.add(j);
                            break;
                        }
                    }
                    if(!found) {
                        List<Integer> list = new ArrayList<>();
                        list.add(j);
                        partitions.add(list);
                    }
                }
            }
            for (List<Integer> partition : partitions) {
                encodedRelationWrapper.getSolver().add(Imply(t.get(TupleN.of(i)).getRef(), Or(partition.stream().map(j -> t.get(TupleN.of(j)).getRef()).collect(Collectors.toList()))));
            }
        }
        return getOrCreate(encodedRelationWrapper, idList, "rf", false);
    }

    Long commit = null;
    public boolean nextSolution(Collection<Map<Decl<?>, LitExpr<?>>> solutions) {
        if(commit != null) currentModel = modelStore.createModel(commit);
        else commit = currentModel.commit();
        if(encodedRelationWrapper.getSolver().check().isSat()) {
            solutions.add(Map.copyOf(encodedRelationWrapper.getSolver().getModel().toMap()));
            final EventConstantLookup rf = encodedRelationWrapper.getEventLookup("rf");

            final Map<Decl<?>, LitExpr<?>> lut = encodedRelationWrapper.getSolver().getModel().toMap();
            final List<Expr<BoolType>> subexprs = new ArrayList<>();

            rf.getAll().forEach((tuple, constDecl) -> {
                if(lut.get(constDecl).equals(True())) {
                    subexprs.add(constDecl.getRef());
                    setTrue("rf", tuple.get(0), tuple.get(1));
                }
                else subexprs.add(Not(constDecl.getRef()));
            });


            encodedRelationWrapper.getSolver().add(Not(And(subexprs)));

            return true;
        }
        return false;
    }

    public Collection<Tuple> getRf() {
        return getMustValues(rel("rf"));
    }

    // Builder methods

    public void addDataDependency(final int i, final int j) {
        setTrue("data", i, j);
    }


    public int addWrite(final int processId, final int varId, final int lastNode, final Collection<String> tags) {
        check(processId, varId, lastNode, tags);
        final int id = addMemoryEvent(processId, varId, lastNode);
        setTrue("W", id);
        return id;
    }

    public int addRead(final int processId, final int varId, final int lastNode, final Collection<String> tags) {
        check(processId, varId, lastNode, tags);
        final int id = addMemoryEvent(processId, varId, lastNode);
        setTrue("R", id);
        return id;
    }

    public int addFence(final int processId, final int lastNode, final Collection<String> tags) {
        check(processId, -1, lastNode, tags);
        final int id = addNormalEvent(processId, lastNode);
        setTrue("F", id);
        return id;
    }

    public int addInitialWrite(final int varId, final Collection<String> tags) {
        check(-1, varId, 0, tags);
        final int id = addAnyEvent();
        setTrue("W", id);
        setTrue("IW", id);
        setTrue("M", id);
        setTrue("loc-raw", varId, id);
        return id;
    }

    public void mustInclude(final int id) {
        setTrue("in-trace", id);
    }

    // support methods for builders

    private int addMemoryEvent(int processId, int varId, int lastNode) {
        final int id = addNormalEvent(processId, lastNode);
        setTrue("M", id);
        setTrue("loc-raw", varId, id);
        return id;
    }

    private int addNormalEvent(int processId, int lastNode) {
        final int id = addAnyEvent();
        if(lastNode == 0) {
            for (final Tuple iw : getMustValues(rel("IW"))) {
                setTrue("po", unbox(iw), id);
            }
        } else {
            setTrue("po", lastNode, id);
        }
        setTrue("int-raw", processId, id);
        return id;
    }

    private int addAnyEvent() {
        final int id = lastCnt++;
        setTrue("id", id, id);
        setTrue("U", id);
        return id;
    }

    // HELPER METHODS

    public Relation<TruthValue> rel(final String s) {
        if(tags.containsKey(s)) return tags.get(s);
        return preDefinedRelations.get(s);
    }

    public void setTrue(final String s, final int... i) {
        final Tuple t = Tuple.of(i);
        currentModel.put(rel(s), t, TruthValue.TRUE);
    }

    private Collection<Tuple> getMustValues(final DataRepresentation<Tuple, TruthValue> rel) {
        final Cursor<Tuple, TruthValue> cursor = currentModel.getAll(rel);
        cursor.move();
        final Collection<Tuple> ret = new LinkedHashSet<>();
        while(!cursor.isTerminated()) {
            if(cursor.getValue().must()) ret.add(cursor.getKey());
            cursor.move();
        }
        return ret;
    }

    private int unbox(final Tuple unaryTuple) {
        checkArgument(unaryTuple.getSize() == 1);
        return unaryTuple.get(0);
    }


    private void check(int processId, int varId, int lastNode, Collection<String> tags) {
        checkArgument(processId < 0, "Meta IDs should be negative!");
        checkArgument(varId < 0, "Meta IDs should be negative!");
        checkArgument(lastNode >= 0, "Only meta IDs should be negative!");
        checkArgument(tags.stream().allMatch(this.tags::containsKey), "All tags should have been initialized!");
    }

    private EventConstantLookup getOrCreate(
            final EncodedRelationWrapper encodedRelationWrapper,
            final List<Integer> idList,
            final String name,
            final boolean isUnary) {
        EventConstantLookup lookup = encodedRelationWrapper.getEventLookup(name);
        if(lookup == null) {
            lookup = createDummyRelation(idList, name, isUnary);
            encodedRelationWrapper.addEvent(name, lookup);
        }
        return lookup;
    }

    private EventConstantLookup createDummyRelation(List<Integer> idList, String name, boolean isUnary) {
        EventConstantLookup eventConstantLookup = new EventConstantLookup();
        for (final int i : idList) {
            if(isUnary) {
                eventConstantLookup.add(TupleN.of(i), Const(name + "_" + i, Bool()));
            }
            else {
                for (final int j : idList) {
                    eventConstantLookup.add(TupleN.of(i, j), Const(name + "_" + i + "_" + j, Bool()));
                }
            }
        }
        return eventConstantLookup;
    }


    private void updateCalculatedRelations() {
        final Collection<Tuple> poRawValues = getMustValues(rel("po-raw"));
        final Relation<TruthValue> po = rel("po");

        final Collection<Tuple> intRawValues = getMustValues(rel("int-raw"));
        final Relation<TruthValue> _int = rel("int");

        final Collection<Tuple> locRawValues = getMustValues(rel("loc-raw"));
        final Relation<TruthValue> loc = rel("loc");

        final Datalog program = Datalog.createProgram();
        final Datalog.Relation poRaw = program.createRelation("po-raw", 2);
        final Datalog.Relation intRaw = program.createRelation("int-raw", 2);
        final Datalog.Relation locRaw = program.createRelation("loc-raw", 2);
        final Datalog.Relation poRel = program.createTransitive("po", poRaw);
        final Datalog.Relation intRel = program.createCommonSource("int", intRaw);
        final Datalog.Relation locRel = program.createCommonSource("loc", locRaw);

        poRawValues.forEach(v -> poRaw.addFact(tup(v)));
        intRawValues.forEach(v -> intRaw.addFact(tup(v)));
        locRawValues.forEach(v -> locRaw.addFact(tup(v)));

        poRel.getElements().forEach(t -> currentModel.put(po, tup(t), TruthValue.TRUE));
        intRel.getElements().forEach(t -> currentModel.put(_int, tup(t), TruthValue.TRUE));
        locRel.getElements().forEach(t -> currentModel.put(loc, tup(t), TruthValue.TRUE));
    }

    private Tuple tup(TupleN<DatalogArgument> t) {
        if(t.arity() == 1) return Tuple.of(((GenericDatalogArgument<Integer>)t.get(0)).getContent());
        if(t.arity() == 2) return Tuple.of(((GenericDatalogArgument<Integer>)t.get(0)).getContent(), ((GenericDatalogArgument<Integer>)t.get(1)).getContent());
        throw new UnsupportedOperationException("Relations with higher arities not supported");
    }
    private Tuple itup(TupleN<Integer> t) {
        if(t.arity() == 1) return Tuple.of(t.get(0));
        if(t.arity() == 2) return Tuple.of(t.get(0), t.get(1));
        throw new UnsupportedOperationException("Relations with higher arities not supported");
    }

    private TupleN<DatalogArgument> tup(Tuple t) {
        if(t.getSize() == 1) return TupleN.of(GenericDatalogArgument.createArgument(t.get(0)));
        if(t.getSize() == 2) return TupleN.of(GenericDatalogArgument.createArgument(t.get(0)), GenericDatalogArgument.createArgument(t.get(1)));
        throw new UnsupportedOperationException("Relations with higher arities not supported");
    }
}
