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
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.mcm.*;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.GenericDatalogArgument;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.UCSolver;
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
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public class AbstractExecutionGraph<S extends State, A extends StmtAction> {
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
    private final Map<Integer, ARG<S, ActionUnion<A>>> threadArgs;
    private final Map<Integer, ArgNode<S, ActionUnion<A>>> argNodeLookup;
    private final PartialOrd<S> partialOrd;
    private final Map<Integer, Integer> lastMemEventLookup;
    private final Map<Integer, MemoryEvent> memoryEventLookup;

    public AbstractExecutionGraph(final Collection<String> tags, final Solver solver, final MCM mcm, final PartialOrd<S> partialOrd) {
        this.mcm = mcm;
        this.partialOrd = partialOrd;
        this.tags = new LinkedHashMap<>();
        tags.forEach(t -> this.tags.put(t, new Relation<>(t, 1, TruthValue.FALSE)));
        modelStore = new ModelStoreImpl(Sets.union(Set.copyOf(this.tags.values()), Set.copyOf(preDefinedRelations.values())));
        currentModel = modelStore.createModel();
        encodedRelationWrapper = new EncodedRelationWrapper(solver);
        threadArgs = new LinkedHashMap<>();
        argNodeLookup = new LinkedHashMap<>();
        lastMemEventLookup = new LinkedHashMap<>();
        memoryEventLookup = new LinkedHashMap<>();
    }

    // Encoder method

    public EventConstantLookup encode() {
        updateCalculatedRelations(); // this won't be necessary when Refinery will support derivation rules

        final List<Integer> idList = getMustValues(rel("U")).stream().map(this::unbox).collect(Collectors.toList());

        for (final MCMConstraint constraint : mcm.getConstraints()) {
            constraint.encodeEvents(idList, encodedRelationWrapper);
        }
        Solver solver = encodedRelationWrapper.getSolver();

        final Collection<Relation<TruthValue>> binaryRelations = preDefinedRelations.values().stream().filter(r -> r.getArity() == 2).toList();
        final Collection<Relation<TruthValue>> unaryRelations = Sets.union(Set.copyOf(tags.values()), preDefinedRelations.values().stream().filter(r -> r.getArity() == 1).collect(Collectors.toSet()));

        for (final int i : idList) {
            for (final Relation<TruthValue> unaryRelation : unaryRelations) {
                TruthValue truthValue = currentModel.get(unaryRelation, Tuple.of(i));
                if(truthValue.must()) {
                    solver.add(getOrCreate(encodedRelationWrapper, idList, unaryRelation.getName(), true).get(TupleN.of(i)).getRef());
                } else if(!truthValue.may()) {
                    solver.add(Not(getOrCreate(encodedRelationWrapper, idList, unaryRelation.getName(), true).get(TupleN.of(i)).getRef()));
                }
            }
            for (final int j : idList) {
                for (final Relation<TruthValue> binaryRelation : binaryRelations) {
                    TruthValue truthValue = currentModel.get(binaryRelation, Tuple.of(i, j));
                    if(truthValue.must()) {
                        solver.add(getOrCreate(encodedRelationWrapper, idList, binaryRelation.getName(), false).get(TupleN.of(i, j)).getRef());
                    } else if(!truthValue.may()) {
                        solver.add(Not(getOrCreate(encodedRelationWrapper, idList, binaryRelation.getName(), false).get(TupleN.of(i, j)).getRef()));
                    }
                }
            }
        }

        // special encoding is necessary to ensure a maximal set of events are in-trace:
        EventConstantLookup t = getOrCreate(encodedRelationWrapper, idList, "T", true);
        for (final int i : idList) {
            List<List<Integer>> partitions = new ArrayList<>();
            if(currentModel.get(rel("IW"), Tuple.of(i)).must()) solver.add(t.get(TupleN.of(i)).getRef());

            for (final int j : idList) {
                if(currentModel.get(rel("po-raw"), Tuple.of(i, j)).must()) {
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
                solver.add(Imply(t.get(TupleN.of(i)).getRef(), Or(partition.stream().map(j -> t.get(TupleN.of(j)).getRef()).collect(Collectors.toList()))));
                for (final int j : partition) {
                    solver.add(Imply(t.get(TupleN.of(j)).getRef(), t.get(TupleN.of(i)).getRef()));
                    solver.add(Imply(t.get(TupleN.of(j)).getRef(), Not(Or(partition.stream().filter(k -> k!=j).map(k -> t.get(TupleN.of(k)).getRef()).collect(Collectors.toList())))));
                }
            }
        }
        final EventConstantLookup rf = getOrCreate(encodedRelationWrapper, idList, "rf", false);

        final Map<Integer, Expr<?>> writeVarIndexingMap = new LinkedHashMap<>();
        final Map<Integer, Expr<?>> readVarIndexingMap = new LinkedHashMap<>();


        // problem: branches should use the same origin indexing but a different target indexing
        // Otherwise L1 -> [x := y] -> L2; L1 -> [x := -y] -> L2 is not solvable

        threadArgs.forEach((pid, arg) -> {
            encodeArg(solver, t, writeVarIndexingMap, readVarIndexingMap, arg);
        });

        writeVarIndexingMap.forEach((i, writeConst) -> readVarIndexingMap.forEach((j, readConst) ->
                solver.add(Imply(rf.get(TupleN.of(i, j)).getRef(), Eq(writeConst, readConst)))));


        printUC(solver);


        return rf;
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


    public boolean tryCover(int pid, int id) {
        checkState(threadArgs.containsKey(pid));
        final ARG<S, ActionUnion<A>> arg = threadArgs.get(pid);
        final ArgNode<S, ActionUnion<A>> node = argNodeLookup.get(id);
        final Optional<ArgNode<S, ActionUnion<A>>> covering = arg.getNodes().filter(argNode -> argNode.mayCover(node)).findFirst();
        if(covering.isEmpty()) return false;
        else {
            covering.get().cover(node);
            return true;
        }
    }

    public void addDataDependency(final int i, final int j) {
        setTrue("data", i, j);
    }

    public int addMemoryEvent(final MemoryEvent memoryEvent, final int pid, final int lastId) {
        checkState(threadArgs.containsKey(pid));
        final int actualLastId = getActualLastId(lastId);
        int id = switch (memoryEvent.type()) {
            case READ -> addRead(pid, memoryEvent.asRead().varId(), actualLastId, Set.of(memoryEvent.tag()));
            case WRITE -> addWrite(pid, memoryEvent.asWrite().varId(), actualLastId, Set.of(memoryEvent.tag()));
            case FENCE -> addFence(pid, actualLastId, Set.of(memoryEvent.tag()));
        };
        final ArgNode<S, ActionUnion<A>> lastArgNode = argNodeLookup.get(lastId);
        final ArgNode<S, ActionUnion<A>> succNode = threadArgs.get(pid).createSuccNode(lastArgNode, new ActionUnion.MemoryEventAction<>(memoryEvent, id), lastArgNode.getState(), false);
        argNodeLookup.put(id, succNode);
        memoryEventLookup.put(id, memoryEvent);
        return id;
    }

    private int getActualLastId(int lastId) {
        if(lastMemEventLookup.containsKey(lastId)) {
            return getActualLastId(lastMemEventLookup.get(lastId));
        } else return lastId;
    }

    private int addWrite(final int processId, final int varId, final int lastNode, final Collection<String> tags) {
        check(processId, varId, lastNode, tags);
        final int id = addMemoryEvent(processId, varId, lastNode, tags);
        setTrue("W", id);
        return id;
    }

    private int addRead(final int processId, final int varId, final int lastNode, final Collection<String> tags) {
        check(processId, varId, lastNode, tags);
        final int id = addMemoryEvent(processId, varId, lastNode, tags);
        setTrue("R", id);
        return id;
    }

    private int addFence(final int processId, final int lastNode, final Collection<String> tags) {
        check(processId, -1, lastNode, tags);
        final int id = addNormalEvent(processId, lastNode, tags);
        setTrue("F", id);
        return id;
    }

    public int addInitialWrite(final int varId, final Collection<String> tags) {
        check(-1, varId, 0, tags);
        final int id = addAnyEvent(tags);
        setTrue("W", id);
        setTrue("IW", id);
        setTrue("M", id);
        setTrue("loc-raw", varId, id);
        return id;
    }

    public int addInitialState(final int pid, final S state, final boolean target) {
        if(!threadArgs.containsKey(pid)) {
            threadArgs.put(pid, ARG.create(partialOrd));
        }
        final int id = lastCnt++;
        lastMemEventLookup.put(id, 0);
        ArgNode<S, ActionUnion<A>> initNode = threadArgs.get(pid).createInitNode(state, target);
        argNodeLookup.put(id, initNode);
        return id;
    }

    public int addState(final int lastNode, final int pid, final A action, final S state, final boolean target) {
        checkState(threadArgs.containsKey(pid));
        final int id = lastCnt++;
        lastMemEventLookup.put(id, lastNode);
        ArgNode<S, ActionUnion<A>> succNode = threadArgs.get(pid).createSuccNode(argNodeLookup.get(lastNode), new ActionUnion.ActionWrapper<>(action), state, target);
        argNodeLookup.put(id, succNode);
        return id;
    }

    // support methods for builders

    private int addMemoryEvent(int processId, int varId, int lastNode, Collection<String> tags) {
        final int id = addNormalEvent(processId, lastNode, tags);
        setTrue("M", id);
        setTrue("loc-raw", varId, id);
        return id;
    }

    private int addNormalEvent(int processId, int lastNode, Collection<String> tags) {
        final int id = addAnyEvent(tags);
        if(lastNode == 0) {
            for (final Tuple iw : getMustValues(rel("IW"))) {
                setTrue("po-raw", unbox(iw), id);
            }
        } else {
            setTrue("po-raw", lastNode, id);
        }
        setTrue("int-raw", processId, id);
        return id;
    }

    private int addAnyEvent(Collection<String> tags) {
        final int id = lastCnt++;
        setTrue("id", id, id);
        setTrue("U", id);
        tags.forEach(s -> setTrue(s, id));
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

    private void printUC(Solver solver) {
        if(solver.check().isUnsat()) {
            try(final UCSolver ucSolver = SolverManager.resolveSolverFactory("Z3").createUCSolver()) {
                ucSolver.track(solver.getAssertions());
                ucSolver.check();
                for (Expr<BoolType> boolTypeExpr : ucSolver.getUnsatCore()) {
                    System.err.println(boolTypeExpr);
                }
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
    }

    private void encodeArg(Solver solver, EventConstantLookup t, Map<Integer, Expr<?>> writeVarIndexingMap, Map<Integer, Expr<?>> readVarIndexingMap, ARG<S, ActionUnion<A>> arg) {
        final Collection<Tuple2<ArgNode<S, ActionUnion<A>>, VarIndexing>> waitSet = new LinkedHashSet<>();
        arg.getInitNodes().forEach(node -> waitSet.add(Tuple2.of(node, VarIndexingFactory.indexing(0))));
        VarIndexing lhsIndexing = VarIndexingFactory.indexing(0);
        while(!waitSet.isEmpty()) {
            final Tuple2<ArgNode<S, ActionUnion<A>>, VarIndexing> nextElement = waitSet.stream().findAny().get();
            waitSet.remove(nextElement);
            final ArgNode<S, ActionUnion<A>> node = nextElement.get1();
            final VarIndexing rhsIndexing = nextElement.get2();

            for (ArgEdge<S, ActionUnion<A>> argEdge : node.getOutEdges().toList()) {
                final ActionUnion<A> actionOrMemEvent = argEdge.getAction();
                if(actionOrMemEvent.isMemoryEvent()) {
                    VarIndexing localIndexing = rhsIndexing;
                    MemoryEvent memoryEvent = actionOrMemEvent.asMemoryEventAction().getMemoryEvent();
                    switch(memoryEvent.type()) {
                        case READ -> {
                            lhsIndexing = lhsIndexing.inc(memoryEvent.asRead().localVar());
                            localIndexing = localIndexing.inc(memoryEvent.asRead().localVar(), lhsIndexing.get(memoryEvent.asRead().localVar()) - localIndexing.get(memoryEvent.asRead().localVar()));
                            readVarIndexingMap.put(actionOrMemEvent.asMemoryEventAction().getId(), PathUtils.unfold(memoryEvent.asRead().localVar().getRef(), localIndexing));
                        }
                        case WRITE -> writeVarIndexingMap.put(actionOrMemEvent.asMemoryEventAction().getId(), PathUtils.unfold(memoryEvent.asWrite().localVar().getRef(), localIndexing));
                        default -> {}
                    }
                    waitSet.add(Tuple2.of(argEdge.getTarget(), localIndexing));
                }
                if(!actionOrMemEvent.isMemoryEvent()) {
                    final A action = actionOrMemEvent.asActionWrapper().getAction();
                    VarIndexing localIndexing = rhsIndexing;
                    for (Stmt stmt : action.getStmts()) {
                        Tuple3<Collection<Expr<BoolType>>, VarIndexing, VarIndexing> unfoldResult = StmtTreeUnfolder.unfold(stmt, lhsIndexing, localIndexing);
                        Expr<BoolType> base = Or(collectImmediateSuccessors(argEdge).stream().map(i -> t.get(TupleN.of(i)).getRef()).toList());
                        solver.add(Imply(base, And(unfoldResult.get1())));
                        lhsIndexing = unfoldResult.get2();
                        localIndexing = unfoldResult.get3();
                    }
                    waitSet.add(Tuple2.of(argEdge.getTarget(), localIndexing));
                }
            }
        }
    }

    private Set<Integer> collectImmediateSuccessors(final ArgEdge<S, ActionUnion<A>> edge) {
        if(edge.getAction().isMemoryEvent) {
            return Set.of(edge.getAction().asMemoryEventAction().getId());
        } else {
            final Set<Integer> ret = new LinkedHashSet<>();
            for (ArgEdge<S, ActionUnion<A>> outEdge : edge.getTarget().getOutEdges().toList()) {
                ret.addAll(collectImmediateSuccessors(outEdge));
            }
            return ret;
        }
    }

    private static abstract class ActionUnion<A> implements Action {
       private final boolean isMemoryEvent;

       protected ActionWrapper<A> asActionWrapper() {
           throw new ClassCastException("Cannot be cast to ActionWrapper");
       }
       protected MemoryEventAction<A> asMemoryEventAction() {
           throw new ClassCastException("Cannot be cast to MemoryEventAction");
       }

       protected ActionUnion(boolean isMemoryEvent) {
            this.isMemoryEvent = isMemoryEvent;
       }

        public boolean isMemoryEvent() {
            return isMemoryEvent;
        }

        private static final class MemoryEventAction<A> extends ActionUnion<A> {
            private final MemoryEvent memoryEvent;
            private final int id;

            private MemoryEventAction(MemoryEvent memoryEvent, int id) {
                super(true);
                this.memoryEvent = memoryEvent;
                this.id = id;
            }

            public MemoryEvent getMemoryEvent() {
                return memoryEvent;
            }

           @Override
           protected MemoryEventAction<A> asMemoryEventAction() {
               return this;
           }

            public int getId() {
                return id;
            }
        }

        private static final class ActionWrapper<A> extends ActionUnion<A> {
            private final A action;

            private ActionWrapper(A action) {
                super(false);
                this.action = action;
            }

            public A getAction() {
                return action;
            }

            @Override
            protected ActionWrapper<A> asActionWrapper() {
                return this;
            }
        }
    }
}
