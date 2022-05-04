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

package hu.bme.mit.theta.analysis.algorithm.mcm;

import com.google.common.collect.Sets;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.GenericDatalogArgument;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import tools.refinery.store.map.Cursor;
import tools.refinery.store.model.Model;
import tools.refinery.store.model.ModelStore;
import tools.refinery.store.model.ModelStoreImpl;
import tools.refinery.store.model.Tuple;
import tools.refinery.store.model.representation.Relation;
import tools.refinery.store.model.representation.TruthValue;

import java.util.*;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public class ExecutionGraph {
    private final Model model;
    private final Relation<Boolean> po, _int, loc, R, W, F, U;
    private final Map<String, Relation<Boolean>> tags;
    private final Relation<TruthValue> rf, co;
    private final Datalog.Relation poRaw, intRaw, locRaw;
    private final Datalog.Relation poCalculated, intCalculated, locCalculated;
    private int lastCnt = 1;

    public ExecutionGraph(final Collection<String> tags) {
        po = new Relation<>("po", 2, false);
        _int = new Relation<>("_int", 2, false);
        loc = new Relation<>("loc", 2, false);
        R = new Relation<>("R", 1, false);
        W = new Relation<>("W", 1, false);
        F = new Relation<>("F", 1, false);
        U = new Relation<>("U", 1, false);
        rf = new Relation<>("rf", 2, TruthValue.UNKNOWN);
        co = new Relation<>("co", 2, TruthValue.UNKNOWN);
        this.tags = new LinkedHashMap<>();
        tags.forEach(s -> this.tags.put(s, new Relation<>(s, 1, false)));
        final ModelStore store = new ModelStoreImpl(Sets.union(Set.copyOf(this.tags.values()), Set.of(po, _int, loc, R, W, F, U, rf, co)));
        model = store.createModel();
        final Datalog program = Datalog.createProgram();
        poRaw = program.createRelation("po_raw", 2);
        intRaw = program.createRelation("int_raw", 2);
        locRaw = program.createRelation("loc_raw", 2);
        poCalculated = program.createTransitive("po", poRaw);
        intCalculated = program.createCommonSource("int", intRaw);
        locCalculated = program.createCommonSource("loc", locRaw);
    }

    private static TupleN<DatalogArgument> arg(int i, int j) {
        return TupleN.of(GenericDatalogArgument.createArgument(i), GenericDatalogArgument.createArgument(j));
    }

    private int addEvent(int processId, int lastNode, final Collection<String> tags) {
        final int id = lastCnt++;
        if(lastNode > 0) {
            poRaw.addFact(arg(lastNode, id));
        }
        for (final String tag : tags) {
            final Relation<Boolean> relation = checkNotNull(this.tags.get(tag));
            model.put(relation, Tuple.of(id), true);
        }
        intRaw.addFact(arg(processId, id));
        model.put(U, Tuple.of(id), true);
        return id;
    }

    private int addMemoryEvent(int processId, int varId, int lastNode, Relation<Boolean> r, final Collection<String> tags) {
        final int id = addEvent(processId, lastNode, tags);
        locRaw.addFact(arg(varId, id));
        model.put(r, Tuple.of(id), true);
        return id;
    }

    public int addRead(final int processId, final int varId, final int lastNode, final Collection<String> tags) {
        return addMemoryEvent(processId, varId, lastNode, R, tags);
    }

    public int addWrite(final int processId, final int varId, final int lastNode, final Collection<String> tags) {
        return addMemoryEvent(processId, varId, lastNode, W, tags);
    }

    public int addFence(final int processId, final int lastNode, final Collection<String> tags) {
        final int id = addEvent(processId, lastNode, tags);
        model.put(F, Tuple.of(id), true);
        return id;
    }

    public void print() {
        syncDatalogRefinery();
        System.out.println("digraph G{");
        printUnaryRelation(R);
        printUnaryRelation(W);
        printUnaryRelation(F);
        printBinaryRelation(po);
        printBinaryCalculatedRelation(rf);
        printBinaryCalculatedRelation(co);
        System.out.println("}");
    }

    private void syncDatalogRefinery() {
        extractElements(poCalculated, po);
        extractElements(intCalculated, _int);
        extractElements(locCalculated, loc);
    }

    private void extractElements(Datalog.Relation from, Relation<Boolean> to) {
        for (TupleN<DatalogArgument> element : from.getElements()) {
            GenericDatalogArgument<Integer> i = (GenericDatalogArgument<Integer>) element.get(0);
            GenericDatalogArgument<Integer> j = (GenericDatalogArgument<Integer>) element.get(1);
            model.put(to, Tuple.of(i.getContent(), j.getContent()), true);
        }
    }

    private void printUnaryRelation(Relation<Boolean> r) {
        Cursor<Tuple, Boolean> all = model.getAll(r);
        all.move();
        while(!all.isTerminated()) {
            if(all.getValue()) {
                int key = all.getKey().get(0);
                System.out.println(key + "[label=\"" + r.getName() + "\"];");
            }
            all.move();
        }
    }

    private void printBinaryRelation(Relation<Boolean> r) {
        Cursor<Tuple, Boolean> all = model.getAll(r);
        all.move();
        while(!all.isTerminated()) {
            if(all.getValue()) {
                int source = all.getKey().get(0);
                int target = all.getKey().get(1);
                System.out.println(source + " -> " + target + "[label=\"" + r.getName() + "\"];");
            }
            all.move();
        }
    }
    private void printBinaryCalculatedRelation(Relation<TruthValue> r) {
        Cursor<Tuple, TruthValue> all = model.getAll(r);
        all.move();
        while(!all.isTerminated()) {
            int source = all.getKey().get(0);
            int target = all.getKey().get(1);
            String name = "\"" + r.getName() + "\"";
            if(all.getValue() == TruthValue.FALSE) name = "<s>\"" + r.getName() + "\"</s>";
            System.out.println(source + " -> " + target + "[label=" + name + "];");
            all.move();
        }
    }

    private EventConstantLookup getOrCreate(
            final EncodedRelationWrapper encodedRelationWrapper,
            final List<Integer> idList,
            final String name,
            final boolean isUnary) {
        EventConstantLookup lookup = encodedRelationWrapper.getEventLookup(name);
        if(lookup == null) {
            lookup = createDummyRelation(idList, name, isUnary);
        }
        return lookup;
    }


    public Collection<ConstDecl<BoolType>> encode(final MCM mcm, final EncodedRelationWrapper encodedRelationWrapper) {
        syncDatalogRefinery();

        final Cursor<Tuple, Boolean> allEvents = model.getAll(U);
        final List<Integer> idList = new ArrayList<>();
        for(allEvents.move(); !allEvents.isTerminated(); allEvents.move()) {
            if(allEvents.getValue()) idList.add(allEvents.getKey().get(0));
        }

        for (final MCMConstraint constraint : mcm.getConstraints()) {
            constraint.encodeEvents(idList, encodedRelationWrapper);
        }

        EventConstantLookup po = getOrCreate(encodedRelationWrapper, idList, "po", false);
        EventConstantLookup _int = getOrCreate(encodedRelationWrapper, idList, "int", false);
        EventConstantLookup loc = getOrCreate(encodedRelationWrapper, idList, "loc", false);
        EventConstantLookup rf = getOrCreate(encodedRelationWrapper, idList, "rf", false);
        EventConstantLookup co = getOrCreate(encodedRelationWrapper, idList, "co", false);
        EventConstantLookup R = getOrCreate(encodedRelationWrapper, idList, "R", true);
        EventConstantLookup W = getOrCreate(encodedRelationWrapper, idList, "W", true);
        EventConstantLookup F = getOrCreate(encodedRelationWrapper, idList, "F", true);

        for (final int i : idList) {
            encodeUnaryRelation(this.R, encodedRelationWrapper, R, i);
            encodeUnaryRelation(this.W, encodedRelationWrapper, W, i);
            encodeUnaryRelation(this.F, encodedRelationWrapper, F, i);
        }

        encodeRelation(encodedRelationWrapper, idList, this.po, po);
        encodeRelation(encodedRelationWrapper, idList, this._int, _int);
        encodeRelation(encodedRelationWrapper, idList, this.loc, loc);

        for (final int i : idList) {
            addRfConstraints(encodedRelationWrapper, idList, rf, i);
            addCoConstraints(encodedRelationWrapper, idList, co, i);
        }

        return rf.getConstants();
    }

    private void encodeUnaryRelation(Relation<Boolean> rel, EncodedRelationWrapper encodedRelationWrapper, EventConstantLookup R, int i) {
        if(model.get(rel, Tuple.of(i))) {
            encodedRelationWrapper.getSolver().add(R.get(TupleN.of(i)).getRef());
        } else {
            encodedRelationWrapper.getSolver().add(Not(R.get(TupleN.of(i)).getRef()));
        }
    }

    private void encodeRelation(EncodedRelationWrapper encodedRelationWrapper, List<Integer> idList, Relation<Boolean> rel, EventConstantLookup enc) {
        for (final int i : idList) {
            for (final int j : idList) {
                if(model.get(rel, Tuple.of(i, j))) {
                    encodedRelationWrapper.getSolver().add(enc.get(TupleN.of(i, j)).getRef());
                } else {
                    encodedRelationWrapper.getSolver().add(Not(enc.get(TupleN.of(i, j)).getRef()));
                }
            }
        }
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

    private void addCoConstraints(EncodedRelationWrapper encodedRelationWrapper, List<Integer> idList, EventConstantLookup co, int i) {
        if(model.get(W, Tuple.of(i))) {
            final List<Expr<BoolType>> subexprs = new ArrayList<>();
            for (final int j : idList) {
                if(model.get(W, Tuple.of(j)) && model.get(loc, Tuple.of(i, j))) {
                    if(i == j) subexprs.add(Not(co.get(TupleN.of(i, j)).getRef()));
                    else {
                        subexprs.add(Xor(co.get(TupleN.of(i, j)).getRef(), co.get(TupleN.of(j, i)).getRef()));
                        for (final int k : idList) {
                            if (model.get(W, Tuple.of(k)) && i != k && j != k) {
                                final RefExpr<BoolType> a = co.get(TupleN.of(i, k)).getRef();
                                final RefExpr<BoolType> b = co.get(TupleN.of(k, j)).getRef();
                                final RefExpr<BoolType> c = co.get(TupleN.of(i, j)).getRef();
                                subexprs.add(Iff(And(a, b), c));
                            }
                        }
                    }
                } else {
                    encodedRelationWrapper.getSolver().add(Not(co.get(TupleN.of(i, j)).getRef())); // not W->W [samevar]
                }
            }
            encodedRelationWrapper.getSolver().add(And(subexprs));
        } else {
            for (final int j : idList) {
                encodedRelationWrapper.getSolver().add(Not(co.get(TupleN.of(i, j)).getRef())); // not W->W [samevar]
            }
        }
    }

    private void addRfConstraints(EncodedRelationWrapper encodedRelationWrapper, List<Integer> idList, EventConstantLookup rf, int i) {
        if(model.get(R, Tuple.of(i))) {
            final List<Expr<BoolType>> subexprs = new ArrayList<>();
            for (final int j : idList) {
                if(model.get(W, Tuple.of(j)) && model.get(loc, Tuple.of(i, j))) {
                    final List<Expr<BoolType>> innerSubexprs = new ArrayList<>();
                    for (final int k : idList) {
                        if(model.get(W, Tuple.of(k)) && j != k) {
                            innerSubexprs.add(Not(rf.get(TupleN.of(k, i)).getRef()));
                        }
                    }
                    innerSubexprs.add(rf.get(TupleN.of(j, i)).getRef());
                    subexprs.add(And(innerSubexprs));
                } else {
                    encodedRelationWrapper.getSolver().add(Not(rf.get(TupleN.of(j, i)).getRef())); // not W->R [samevar]
                }
            }
            encodedRelationWrapper.getSolver().add(Or(subexprs));
        } else {
            for (final int j : idList) {
                encodedRelationWrapper.getSolver().add(Not(rf.get(TupleN.of(j, i)).getRef())); // not W->R [samevar]
            }
        }
    }
}
