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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public class ExecutionGraph {
    private final Model model;
    private final Relation<Boolean> _int, loc, R, W, F, U;
    private final Relation<TruthValue> rf, co;
    private final Datalog.Relation poRaw;
    private final Datalog.Relation poCalculated;
    private int lastCnt = 1025; // will support a maximum of 1024 threads

    public ExecutionGraph() {
        _int = new Relation<>("int", 2, false);
        loc = new Relation<>("loc", 2, false);
        R = new Relation<>("R", 1, false);
        W = new Relation<>("W", 1, false);
        F = new Relation<>("F", 1, false);
        U = new Relation<>("U", 1, false);
        rf = new Relation<>("rf", 2, TruthValue.UNKNOWN);
        co = new Relation<>("co", 2, TruthValue.UNKNOWN);
        final ModelStore store = new ModelStoreImpl(Set.of(_int, loc, R, W, F, U, rf, co));
        model = store.createModel();
        final Datalog program = Datalog.createProgram();
        poRaw = program.createRelation("po_raw", 2);
        poCalculated = program.createTransitive("po", poRaw);
    }

    private int addEvent(int processId, int lastNode) {
        final int id = lastCnt++;
        if(lastNode > 0) {
            poRaw.addFact(TupleN.of(GenericDatalogArgument.createArgument(lastNode), GenericDatalogArgument.createArgument(id)));
        }
        model.put(_int, Tuple.of(processId, id), true);
        model.put(U, Tuple.of(id), true);
        return id;
    }

    private int addMemoryEvent(int processId, int varId, int lastNode, Relation<Boolean> r) {
        final int id = addEvent(processId, lastNode);
        model.put(loc, Tuple.of(varId, id), true);
        model.put(r, Tuple.of(id), true);
        return id;
    }

    public int addRead(final int processId, final int varId, final int lastNode) {
        return addMemoryEvent(processId, varId, lastNode, R);
    }

    public int addWrite(final int processId, final int varId, final int lastNode) {
        return addMemoryEvent(processId, varId, lastNode, W);
    }

    public int addFence(final int processId, final int lastNode) {
        final int id = addEvent(processId, lastNode);
        model.put(F, Tuple.of(id), true);
        return id;
    }

    public void print() {
        System.out.println("digraph G{");
        printUnaryRelation(R);
        printUnaryRelation(W);
        printUnaryRelation(F);
//        printBinaryRelation(po);
        System.out.println("}");
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


    public Collection<ConstDecl<BoolType>> encode(final MCM mcm, final EncodedRelationWrapper encodedRelationWrapper) {
        final Cursor<Tuple, Boolean> allEvents = model.getAll(U);
        final List<Integer> idList = new ArrayList<>();
        for(allEvents.move(); !allEvents.isTerminated(); allEvents.move()) {
            if(allEvents.getValue()) idList.add(allEvents.getKey().get(0));
        }

        for (final MCMConstraint constraint : mcm.getConstraints()) {
            constraint.encodeEvents(idList, encodedRelationWrapper);
        }

        EventConstantLookup po = encodedRelationWrapper.getEventLookup("po");
        EventConstantLookup rf = encodedRelationWrapper.getEventLookup("rf");
        EventConstantLookup co = encodedRelationWrapper.getEventLookup("co");

        if(po == null) po = createDummyRelation(idList, "po");
        if(rf == null) rf = createDummyRelation(idList, "rf");
        if(co == null) co = createDummyRelation(idList, "co");

        Collection<TupleN<DatalogArgument>> elements = poCalculated.getElements();
        for (final int _i : idList) {
            final GenericDatalogArgument<Integer> i = GenericDatalogArgument.createArgument(_i);
            for (final int _j : idList) {
                final GenericDatalogArgument<Integer> j = GenericDatalogArgument.createArgument(_j);
                if(elements.contains(TupleN.of(i, j))) {
                    encodedRelationWrapper.getSolver().add(po.get(TupleN.of(_i, _j)).getRef());
                } else {
                    encodedRelationWrapper.getSolver().add(Not(po.get(TupleN.of(_i, _j)).getRef()));
                }
            }
        }

        for (final int i : idList) {
            addRfConstraints(encodedRelationWrapper, idList, rf, i);
            addCoConstraints(encodedRelationWrapper, idList, co, i);
        }

        return rf.getConstants();
    }

    private EventConstantLookup createDummyRelation(List<Integer> idList, String name) {
        EventConstantLookup eventConstantLookup = new EventConstantLookup();
        for (final int i : idList) {
            for (final int j : idList) {
                eventConstantLookup.add(TupleN.of(i, j), Const(name + "_" + i + "_" + j, Bool()));
            }
        }
        return eventConstantLookup;
    }

    private void addCoConstraints(EncodedRelationWrapper encodedRelationWrapper, List<Integer> idList, EventConstantLookup co, int i) {
        if(model.get(W, Tuple.of(i))) {
            final List<Expr<BoolType>> subexprs = new ArrayList<>();
            for (final int j : idList) {
                if(model.get(W, Tuple.of(j))) {
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
                    encodedRelationWrapper.getSolver().add(Not(co.get(TupleN.of(i, j)).getRef())); // not W->W
                }
            }
            encodedRelationWrapper.getSolver().add(And(subexprs));
        } else {
            for (final int j : idList) {
                encodedRelationWrapper.getSolver().add(Not(co.get(TupleN.of(i, j)).getRef())); // not W->W
            }
        }
    }

    private void addRfConstraints(EncodedRelationWrapper encodedRelationWrapper, List<Integer> idList, EventConstantLookup rf, int i) {
        if(model.get(R, Tuple.of(i))) {
            final List<Expr<BoolType>> subexprs = new ArrayList<>();
            for (final int j : idList) {
                if(model.get(W, Tuple.of(j))) {
                    final List<Expr<BoolType>> innerSubexprs = new ArrayList<>();
                    for (final int k : idList) {
                        if(model.get(W, Tuple.of(k)) && j != k) {
                            innerSubexprs.add(Not(rf.get(TupleN.of(k, i)).getRef()));
                        }
                    }
                    innerSubexprs.add(rf.get(TupleN.of(j, i)).getRef());
                    subexprs.add(And(innerSubexprs));
                } else {
                    encodedRelationWrapper.getSolver().add(Not(rf.get(TupleN.of(j, i)).getRef())); // not W->R
                }
            }
            encodedRelationWrapper.getSolver().add(Or(subexprs));
        } else {
            for (final int j : idList) {
                encodedRelationWrapper.getSolver().add(Not(rf.get(TupleN.of(j, i)).getRef())); // not W->R
            }
        }
    }
}
