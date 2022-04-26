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

import tools.refinery.store.map.Cursor;
import tools.refinery.store.model.Model;
import tools.refinery.store.model.ModelStore;
import tools.refinery.store.model.ModelStoreImpl;
import tools.refinery.store.model.Tuple;
import tools.refinery.store.model.representation.Relation;
import tools.refinery.store.model.representation.TruthValue;

import java.util.Set;

public class ExecutionGraph {
    private final Model model;
    private final Relation<Boolean> po, _int, loc, R, W, F;
    private final Relation<TruthValue> rf, co;

    private int lastCnt = 1025; // will support a maximum of 1024 threads

    public ExecutionGraph() {
        po = new Relation<>("po", 2, false);
        _int = new Relation<>("int", 2, false);
        loc = new Relation<>("loc", 2, false);
        R = new Relation<>("R", 1, false);
        W = new Relation<>("W", 1, false);
        F = new Relation<>("F", 1, false);
        rf = new Relation<>("rf", 2, TruthValue.UNKNOWN);
        co = new Relation<>("co", 2, TruthValue.UNKNOWN);
        final ModelStore store = new ModelStoreImpl(Set.of(po, _int, loc, R, W, F, rf, co));
        model = store.createModel();
    }

    private int addEvent(int processId, int lastNode) {
        final int id = lastCnt++;
        if(lastNode > 0) {
            model.put(po, Tuple.of(lastNode, id), true);
        }
        model.put(_int, Tuple.of(processId, id), true);
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
        printBinaryRelation(po);
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
}
