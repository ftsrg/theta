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

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

public class ExecutionGraphBuilder {
    private final Datalog program;
    private final Datalog.Relation initWrite, poRaw, /*TODO: remove */poCalculated, intRaw, intCalculated, locRaw, locCalculated, R, W, F, U, data, addr, ctrl, rmw, amo;
    private final Map<String, Datalog.Relation> tags;
    private int lastCnt = 1;

    public ExecutionGraphBuilder() {
        program = Datalog.createProgram();
        initWrite = program.createRelation("IW", 1);
        poRaw = program.createRelation("po_raw", 2);
        intRaw = program.createRelation("int_raw", 2);
        locRaw = program.createRelation("loc_raw", 2);
        R = program.createRelation("R", 1);
        W = program.createRelation("W", 1);
        F = program.createRelation("F", 1);
        U = program.createRelation("U", 1);
        data = program.createRelation("data", 2);
        addr = program.createRelation("addr", 2);
        ctrl  = program.createRelation("ctrl", 2);
        rmw = program.createRelation("rmw", 2);
        amo = program.createRelation("amo", 2);
        this.tags = new LinkedHashMap<>();

        poCalculated = program.createRelation("po", 2);
        intCalculated = program.createCommonSource("int", intRaw);
        locCalculated = program.createCommonSource("loc", locRaw);
    }

    private static TupleN<DatalogArgument> arg(int i, int j) {
        return TupleN.of(GenericDatalogArgument.createArgument(i), GenericDatalogArgument.createArgument(j));
    }
    private static TupleN<DatalogArgument> arg(int i) {
        return TupleN.of(GenericDatalogArgument.createArgument(i));
    }

    private int addEvent(int processId, int lastNode, final Collection<String> tags) {
        final int id = lastCnt++;
        if(lastNode > 0) {
            poRaw.addFact(arg(lastNode, id));
        } else {
            for (TupleN<DatalogArgument> element : initWrite.getElements()) {
                int iw = ((GenericDatalogArgument<Integer>) element.get(0)).getContent();
                poRaw.addFact(arg(iw, id));
            }
        }
        for (final String tag : tags) {
            this.tags.putIfAbsent(tag, program.createRelation(tag, 1));
            final Datalog.Relation relation = this.tags.get(tag);
            relation.addFact(arg(id));
        }
        intRaw.addFact(arg(processId, id));
        U.addFact(arg(id));
        return id;
    }

    private int addMemoryEvent(int processId, int varId, int lastNode, Datalog.Relation rel, final Collection<String> tags) {
        final int id = addEvent(processId, lastNode, tags);
        locRaw.addFact(arg(varId, id));
        rel.addFact(arg(id));
        return id;
    }

    public int addRead(final int processId, final int varId, final int lastNode, final Collection<String> tags) {
        return addMemoryEvent(processId, varId, lastNode, R, tags);
    }

    public int addWrite(final int processId, final int varId, final int lastNode, final Collection<String> tags) {
        return addMemoryEvent(processId, varId, lastNode, W, tags);
    }

    public void addDependency(int read, int write) {
        data.addFact(arg(read, write));
    }

    public int addInitialWrite(final int varId) {
        final int id = lastCnt++;
        locRaw.addFact(arg(varId, id));
        initWrite.addFact(arg(id));
        W.addFact(arg(id));
        U.addFact(arg(id));
        return id;
    }

    public int addFence(final int processId, final int lastNode, final Collection<String> tags) {
        final int id = addEvent(processId, lastNode, tags);
        F.addFact(arg(id));
        return id;
    }

    public Datalog.Relation getPoRaw() {
        return poRaw;
    }

    public Datalog.Relation getPoCalculated() {
        return poCalculated;
    }

    public Datalog.Relation getIntRaw() {
        return intRaw;
    }

    public Datalog.Relation getIntCalculated() {
        return intCalculated;
    }

    public Datalog.Relation getLocRaw() {
        return locRaw;
    }

    public Datalog.Relation getLocCalculated() {
        return locCalculated;
    }

    public Datalog.Relation getData() {
        return data;
    }

    public Datalog.Relation getR() {
        return R;
    }

    public Datalog.Relation getW() {
        return W;
    }

    public Datalog.Relation getF() {
        return F;
    }

    public Datalog.Relation getU() {
        return U;
    }


    public Datalog.Relation getAddr() {
        return addr;
    }

    public Datalog.Relation getCtrl() {
        return ctrl;
    }

    public Datalog.Relation getRmw() {
        return rmw;
    }

    public Datalog.Relation getAmo() {
        return amo;
    }

    public Map<String, Datalog.Relation> getTags() {
        return tags;
    }
}
