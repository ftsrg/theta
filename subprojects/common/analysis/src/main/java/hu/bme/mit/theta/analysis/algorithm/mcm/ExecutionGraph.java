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
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.GenericDatalogArgument;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import tools.refinery.store.map.Cursor;
import tools.refinery.store.model.Model;
import tools.refinery.store.model.ModelStore;
import tools.refinery.store.model.ModelStoreImpl;
import tools.refinery.store.model.Tuple;
import tools.refinery.store.model.representation.Relation;
import tools.refinery.store.model.representation.TruthValue;

import java.util.*;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public class ExecutionGraph {
    private final MCM mcm;
    private final EncodedRelationWrapper encodedRelationWrapper;
    private final ModelStore store;
    private Model model;
    private final Relation<Boolean> po, _int, ext, addr, ctrl, rmw, amo, loc, id, data, R, W, F, U;
    private final Map<String, Relation<Boolean>> tags;
    private final Relation<TruthValue> rf, co;
    private final long staticOnlyCommit;

    public ExecutionGraph(final ExecutionGraphBuilder builder, final MCM mcm, final Solver solver) {
        this.mcm = mcm;
        encodedRelationWrapper = new EncodedRelationWrapper(solver);
        po = new Relation<>("po-raw", 2, false);
        _int = new Relation<>("_int", 2, false);
        ext = new Relation<>("ext", 2, false);
        addr = new Relation<>("addr", 2, false);
        ctrl = new Relation<>("ctrl", 2, false);
        rmw = new Relation<>("rmw", 2, false);
        amo = new Relation<>("amo", 2, false);
        loc = new Relation<>("loc", 2, false);
        id = new Relation<>("id", 2, false);
        data = new Relation<>("data", 2, false);
        R = new Relation<>("R", 1, false);
        W = new Relation<>("W", 1, false);
        F = new Relation<>("F", 1, false);
        U = new Relation<>("U", 1, false);
        rf = new Relation<>("rf", 2, TruthValue.UNKNOWN);
        co = new Relation<>("co", 2, TruthValue.UNKNOWN);
        this.tags = new LinkedHashMap<>();
        builder.getTags().forEach((key, value) -> {
            final Relation<Boolean> rel = new Relation<>(key, 1, false);
            this.tags.put(key, rel);
        });
        store = new ModelStoreImpl(Sets.union(Set.copyOf(this.tags.values()), Set.of(po, _int, ext, addr, ctrl, rmw, amo, loc, id, data, R, W, F, U, rf, co)));
        model = store.createModel();

        builder.getPoRaw().getElements().forEach(elem -> model.put(po, datalog2tup(elem), true));
        builder.getLocCalculated().getElements().forEach(elem -> model.put(loc, datalog2tup(elem), true));
        builder.getIntCalculated().getElements().forEach(elem -> model.put(_int, datalog2tup(elem), true));
        builder.getData().getElements().forEach(elem -> model.put(data, datalog2tup(elem), true));
        builder.getAddr().getElements().forEach(elem -> model.put(addr, datalog2tup(elem), true));
        builder.getCtrl().getElements().forEach(elem -> model.put(ctrl, datalog2tup(elem), true));
        builder.getRmw().getElements().forEach(elem -> model.put(rmw, datalog2tup(elem), true));
        builder.getAmo().getElements().forEach(elem -> model.put(amo, datalog2tup(elem), true));
        builder.getR().getElements().forEach(elem -> model.put(R, datalog2tup(elem), true));
        builder.getW().getElements().forEach(elem -> model.put(W, datalog2tup(elem), true));
        builder.getF().getElements().forEach(elem -> model.put(F, datalog2tup(elem), true));
        Collection<TupleN<DatalogArgument>> intElements = builder.getIntCalculated().getElements();
        builder.getU().getElements().forEach(elem -> {
            model.put(U, datalog2tup(elem), true);
            model.put(id, Tuple.of(datalog2tup(elem).get(0), datalog2tup(elem).get(0)), true);
            builder.getU().getElements().forEach(elem2 -> {
                TupleN<Integer> tuple = tupleN(elem.get(0), elem2.get(0));
                TupleN<DatalogArgument> tupleDA = TupleN.of(GenericDatalogArgument.createArgument(elem.get(0)), GenericDatalogArgument.createArgument(elem2.get(0)));
                if (!intElements.contains(tupleDA)) {
                    model.put(ext, tup(tuple), true);
                }
            });
        });

        builder.getTags().forEach((key, value) -> {
            value.getElements().forEach(elem -> model.put(this.tags.get(key), datalog2tup(elem), true));
        });


        encode();

        staticOnlyCommit = model.commit();
        encodedRelationWrapper.getSolver().push();
    }

    public void reset() {
        model = store.createModel(staticOnlyCommit);
        encodedRelationWrapper.getSolver().pop();
    }

    public boolean nextSolution(final Collection<Map<Decl<?>, LitExpr<?>>> solutions) {
        model = store.createModel(staticOnlyCommit);
        if (encodedRelationWrapper.getSolver().check().isSat()) {
            solutions.add(Map.copyOf(encodedRelationWrapper.getSolver().getModel().toMap()));
            final EventConstantLookup rf = encodedRelationWrapper.getEventLookup("rf");
            final EventConstantLookup co = encodedRelationWrapper.getEventLookup("co");

            final Map<Decl<?>, LitExpr<?>> lut = encodedRelationWrapper.getSolver().getModel().toMap();
            final List<Expr<BoolType>> subexprs = new ArrayList<>();

            rf.getAll().forEach((tuple, constDecl) -> {
                if (lut.get(constDecl).equals(True())) {
                    model.put(this.rf, tup(tuple), TruthValue.TRUE);
                    subexprs.add(constDecl.getRef());
                } else subexprs.add(Not(constDecl.getRef()));
            });
            co.getAll().forEach((tuple, constDecl) -> {
                if (lut.get(constDecl).equals(True()))
                    model.put(this.co, tup(tuple), TruthValue.TRUE);
            });

            encodedRelationWrapper.getSolver().add(Not(And(subexprs)));

            return true;
        }
        return false;
    }

    private TupleN<Integer> tupleN(final DatalogArgument a, final DatalogArgument b) {
        final int i = ((GenericDatalogArgument<Integer>) a).getContent();
        final int j = ((GenericDatalogArgument<Integer>) b).getContent();
        return TupleN.of(i, j);
    }

    private Tuple datalog2tup(final TupleN<DatalogArgument> from) {
        final int i = ((GenericDatalogArgument<Integer>) from.get(0)).getContent();
        if (from.arity() == 1) return Tuple.of(i);
        final int j = ((GenericDatalogArgument<Integer>) from.get(1)).getContent();
        return Tuple.of(i, j);
    }

    private Tuple tup(final TupleN<Integer> from) {
        final int i = from.get(0);
        if (from.arity() == 1) return Tuple.of(i);
        final int j = from.get(1);
        return Tuple.of(i, j);
    }

    private void encode() {
        final Cursor<Tuple, Boolean> allEvents = model.getAll(U);
        final List<Integer> idList = new ArrayList<>();
        for (allEvents.move(); !allEvents.isTerminated(); allEvents.move()) {
            if (allEvents.getValue()) idList.add(allEvents.getKey().get(0));
        }

        for (final MCMConstraint constraint : mcm.getConstraints()) {
            constraint.encodeEvents(idList, encodedRelationWrapper);
        }

        EventConstantLookup po = getOrCreate(encodedRelationWrapper, idList, "po-raw", false);
        EventConstantLookup _int = getOrCreate(encodedRelationWrapper, idList, "int", false);
        EventConstantLookup loc = getOrCreate(encodedRelationWrapper, idList, "loc", false);
        EventConstantLookup data = getOrCreate(encodedRelationWrapper, idList, "data", false);
        EventConstantLookup rmw = getOrCreate(encodedRelationWrapper, idList, "rmw", false);
        EventConstantLookup amo = getOrCreate(encodedRelationWrapper, idList, "amo", false);
        EventConstantLookup ctrl = getOrCreate(encodedRelationWrapper, idList, "ctrl", false);
        EventConstantLookup ext = getOrCreate(encodedRelationWrapper, idList, "ext", false);
        EventConstantLookup addr = getOrCreate(encodedRelationWrapper, idList, "addr", false);
        EventConstantLookup id = getOrCreate(encodedRelationWrapper, idList, "id", false);
        EventConstantLookup rf = getOrCreate(encodedRelationWrapper, idList, "rf", false);
        EventConstantLookup co = getOrCreate(encodedRelationWrapper, idList, "co", false);
        EventConstantLookup R = getOrCreate(encodedRelationWrapper, idList, "R", true);
        EventConstantLookup W = getOrCreate(encodedRelationWrapper, idList, "W", true);
        EventConstantLookup F = getOrCreate(encodedRelationWrapper, idList, "F", true);
        EventConstantLookup U = getOrCreate(encodedRelationWrapper, idList, "U", true);

        for (final int i : idList) {
            encodeUnaryRelation(this.R, encodedRelationWrapper, R, i);
            encodeUnaryRelation(this.W, encodedRelationWrapper, W, i);
            encodeUnaryRelation(this.F, encodedRelationWrapper, F, i);
            encodeUnaryRelation(this.U, encodedRelationWrapper, U, i);
        }
        this.tags.forEach((s, rel) -> {
            EventConstantLookup ecl = getOrCreate(encodedRelationWrapper, idList, s, true);
            for (int i : idList) {
                encodeUnaryRelation(rel, encodedRelationWrapper, ecl, i);
            }
        });


        encodeRelation(encodedRelationWrapper, idList, this._int, _int);
        encodePo(encodedRelationWrapper, idList, this.po, this._int, po);
        encodeRelation(encodedRelationWrapper, idList, this.loc, loc);
        encodeRelation(encodedRelationWrapper, idList, this.id, id);
        encodeRelation(encodedRelationWrapper, idList, this.data, data);
        encodeRelation(encodedRelationWrapper, idList, this.rmw, rmw);
        encodeRelation(encodedRelationWrapper, idList, this.amo, amo);
        encodeRelation(encodedRelationWrapper, idList, this.ctrl, ctrl);
        encodeRelation(encodedRelationWrapper, idList, this.ext, ext);
        encodeRelation(encodedRelationWrapper, idList, this.addr, addr);

        for (final int i : idList) {
            addRfConstraints(encodedRelationWrapper, idList, rf, i);
            addCoConstraints(encodedRelationWrapper, idList, co, i);
        }

        // encode missing relations
        encodedRelationWrapper.getNonEncoded().forEach((key, value) -> {
            final MCMRelation mcmRelation = mcm.getRelations().get(key);
            if (mcmRelation != null && mcmRelation.getRule() == null) {
                final int arity = mcmRelation.getArity();
                EventConstantLookup ecl = getOrCreate(encodedRelationWrapper, idList, key, arity == 1);
                encodedRelationWrapper.setEncoded(ecl);
                for (final int i : idList) {
                    if (arity == 1) {
                        encodedRelationWrapper.getSolver().add(Not(ecl.get(TupleN.of(i)).getRef()));
                    } else {
                        for (final int j : idList) {
                            encodedRelationWrapper.getSolver().add(Not(ecl.get(TupleN.of(i, j)).getRef()));
                        }
                    }
                }
            }

        });
    }

    private void encodePo(EncodedRelationWrapper encodedRelationWrapper, List<Integer> idList, Relation<Boolean> rel, Relation<Boolean> _int, EventConstantLookup enc) {
        encodedRelationWrapper.setEncoded(enc);
        for (final int i : idList) {
            List<Set<Integer>> collectors = new ArrayList<>();
            for (final int j : idList) {
                if (model.get(rel, Tuple.of(i, j))) {
                    boolean foundSet = false;
                    for (Set<Integer> integers : collectors) {
                        if (model.get(_int, Tuple.of(j, integers.stream().findAny().get()))) {
                            integers.add(j);
                            foundSet = true;
                            break;
                        }
                    }
                    if (!foundSet) {
                        Set<Integer> set = new LinkedHashSet<>();
                        set.add(j);
                        collectors.add(set);
                    }
                } else {
                    encodedRelationWrapper.getSolver().add(Not(enc.get(TupleN.of(i, j)).getRef()));
                }
            }
            for (Set<Integer> collector : collectors) {
                if (collector.size() > 1) {
                    encodedRelationWrapper.getSolver().add(Or(collector.stream().map(j -> enc.get(TupleN.of(i, j)).getRef()).collect(Collectors.toList())));
                } else if (collector.size() > 0) {
                    encodedRelationWrapper.getSolver().add(enc.get(TupleN.of(i, collector.stream().findAny().get())).getRef());
                }
            }
        }
    }

    private EventConstantLookup getOrCreate(
            final EncodedRelationWrapper encodedRelationWrapper,
            final List<Integer> idList,
            final String name,
            final boolean isUnary) {
        EventConstantLookup lookup = encodedRelationWrapper.getEventLookup(name);
        if (lookup == null) {
            lookup = createDummyRelation(idList, name, isUnary);
            encodedRelationWrapper.addEvent(name, lookup);
        }
        return lookup;
    }

    private void encodeUnaryRelation(Relation<Boolean> rel, EncodedRelationWrapper encodedRelationWrapper, EventConstantLookup enc, int i) {
        encodedRelationWrapper.setEncoded(enc);
        if (model.get(rel, Tuple.of(i))) {
            encodedRelationWrapper.getSolver().add(enc.get(TupleN.of(i)).getRef());
        } else {
            encodedRelationWrapper.getSolver().add(Not(enc.get(TupleN.of(i)).getRef()));
        }
    }

    private void encodeRelation(EncodedRelationWrapper encodedRelationWrapper, List<Integer> idList, Relation<Boolean> rel, EventConstantLookup enc) {
        encodedRelationWrapper.setEncoded(enc);
        for (final int i : idList) {
            for (final int j : idList) {
                if (model.get(rel, Tuple.of(i, j))) {
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
            if (isUnary) {
                eventConstantLookup.add(TupleN.of(i), Const(name + "_" + i, Bool()));
            } else {
                for (final int j : idList) {
                    eventConstantLookup.add(TupleN.of(i, j), Const(name + "_" + i + "_" + j, Bool()));
                }
            }
        }
        return eventConstantLookup;
    }

    private void addCoConstraints(EncodedRelationWrapper encodedRelationWrapper, List<Integer> idList, EventConstantLookup co, int i) {
        encodedRelationWrapper.setEncoded(co);
        if (model.get(W, Tuple.of(i))) {
            final List<Expr<BoolType>> subexprs = new ArrayList<>();
            for (final int j : idList) {
                if (model.get(W, Tuple.of(j)) && model.get(loc, Tuple.of(i, j))) {
                    if (i == j) subexprs.add(Not(co.get(TupleN.of(i, j)).getRef()));
                    else {
                        subexprs.add(Xor(co.get(TupleN.of(i, j)).getRef(), co.get(TupleN.of(j, i)).getRef()));
                        for (final int k : idList) {
                            if (model.get(W, Tuple.of(k)) && model.get(loc, Tuple.of(i, k)) && i != k && j != k) {
                                final RefExpr<BoolType> a = co.get(TupleN.of(i, k)).getRef();
                                final RefExpr<BoolType> b = co.get(TupleN.of(k, j)).getRef();
                                final RefExpr<BoolType> c = co.get(TupleN.of(i, j)).getRef();
                                subexprs.add(Imply(And(a, b), c));
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
        encodedRelationWrapper.setEncoded(rf);
        if (model.get(R, Tuple.of(i))) {
            final List<Expr<BoolType>> subexprs = new ArrayList<>();
            for (final int j : idList) {
                if (model.get(W, Tuple.of(j)) && model.get(loc, Tuple.of(i, j))) {
                    final List<Expr<BoolType>> innerSubexprs = new ArrayList<>();
                    for (final int k : idList) {
                        if (model.get(W, Tuple.of(k)) && j != k) {
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


    public void print(Map<Integer, VarDecl<?>> vars) {
        System.out.println("digraph G{");
        printEvents(vars);
        printBinaryRelation(po, true);
//        printBinaryRelation(loc, false);
        printBinaryCalculatedRelation(rf, "red");
        printBinaryCalculatedRelation(co, "purple");
        System.out.println("}");
    }

    private void printEvents(Map<Integer, VarDecl<?>> vars) {
        Cursor<Tuple, Boolean> all = model.getAll(U);
        all.move();
        while (!all.isTerminated()) {
            if (all.getValue()) {
                final int key = all.getKey().get(0);
                final String name = whichEvent(all.getKey());
                final String tags = collectTags(all.getKey());
                final VarDecl<?> var = vars.get(key);
                System.out.println(key + "[label=\"" + name + (var == null ? "" : "(" + var.getName() + ")") + tags + "\"];");
            }
            all.move();
        }
    }

    private String collectTags(Tuple key) {
        final List<String> ret = new ArrayList<>();
        tags.forEach((s, booleanRelation) -> {
            if (model.get(booleanRelation, key)) ret.add(s);
        });
        final StringJoiner sj = new StringJoiner(", ", "[", "]");
        return sj.toString();
    }

    private String whichEvent(Tuple key) {
        if (model.get(R, key)) return "R";
        if (model.get(W, key)) return "W";
        if (model.get(F, key)) return "F";
        throw new RuntimeException("Unsupported event type");
    }

    private void printBinaryRelation(Relation<Boolean> r, boolean constraint) {
        Cursor<Tuple, Boolean> all = model.getAll(r);
        all.move();
        while (!all.isTerminated()) {
            if (all.getValue()) {
                int source = all.getKey().get(0);
                int target = all.getKey().get(1);
                System.out.println(source + " -> " + target + "[label=\"" + r.getName() + "\"" + (constraint ? "" : ",constraint=false") + "];");
            }
            all.move();
        }
    }

    private void printBinaryCalculatedRelation(Relation<TruthValue> r, String color) {
        Cursor<Tuple, TruthValue> all = model.getAll(r);
        all.move();
        while (!all.isTerminated()) {
            int source = all.getKey().get(0);
            int target = all.getKey().get(1);
            String name = "\"" + r.getName() + "\"";
            if (all.getValue() == TruthValue.FALSE) name = "<s>\"" + r.getName() + "\"</s>";
            System.out.println(source + " -> " + target + "[label=" + name + ",constraint=false,color=" + color + "];");
            all.move();
        }
    }

    public Collection<Tuple> getRf() {
        final Cursor<Tuple, TruthValue> cursor = model.getAll(rf);
        cursor.move();
        final Collection<Tuple> ret = new ArrayList<>();
        while (!cursor.isTerminated()) {
            if (cursor.getValue().must()) {
                ret.add(cursor.getKey());
            }
            cursor.move();
        }
        return ret;
    }
}
