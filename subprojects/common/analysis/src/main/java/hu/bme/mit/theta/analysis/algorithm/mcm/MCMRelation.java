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

import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class MCMRelation {
    private final int arity;
    private final String name;

    private MCMRule rule;

    public MCMRelation(int arity, String name) {
        this.arity = arity;
        this.name = name;
    }

    public MCMRelation(int arity, String name, MCMRule rule) {
        this(arity, name);
        this.rule = rule;
    }
    public int getArity() {
        return arity;
    }

    public String getName() {
        return name;
    }

    public MCMRule getRule() {
        return rule;
    }

    public void addRule(final MCMRule rule) {
        checkState(this.rule == null, "Rule already set");
        this.rule = rule;
    }

    public void collectRelations(final Map<String, MCMRelation> relations) {
        if(!relations.containsKey(name)) {
            relations.put(name, this);
            if(rule != null) rule.collectRelations(relations);
        } else {
            if(!relations.get(name).equals(this)) throw new RuntimeException("Different definitions for the relation " + name);
        }
    }

    @Override
    public String toString() {
        return "MCMRelation{" +
                "arity=" + arity +
                ", name='" + name + '\'' +
                ", rule=" + rule +
                '}';
    }

    public EventConstantLookup encodeEvents(final List<Integer> idList, final EncodedRelationWrapper encodedRelationWrapper) {
        if(encodedRelationWrapper.getEventLookup(name) != null) return encodedRelationWrapper.getEventLookup(name);

        final EventConstantLookup eventConstantLookup = new EventConstantLookup();
        encodedRelationWrapper.addEvent(name, eventConstantLookup);
        createConstants(idList, eventConstantLookup);

        if(rule != null) rule.encodeEvents(idList, eventConstantLookup, encodedRelationWrapper);
        return eventConstantLookup;
    }

    private void createConstants(List<Integer> idList, EventConstantLookup eventConstantLookup) {
        if(arity == 1) {
            for (final int i : idList) {
                eventConstantLookup.add(TupleN.of(i), Const(name + "_" + i, Bool()));
            }
        } else if (arity == 2) {
            for (final int i : idList) {
                for (final int j : idList) {
                    eventConstantLookup.add(TupleN.of(i, j), Const(name + "_" + i + "_" + j, Bool()));
                }
            }
        } else throw new UnsupportedOperationException("Relations with arity " + arity + " not supported.");
    }
}
