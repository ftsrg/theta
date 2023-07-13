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

package hu.bme.mit.theta.cat.mcm;

import hu.bme.mit.theta.common.TupleN;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Map;

public class MCMRelation {
    private final int arity;
    private final String name;

    private final Collection<TupleN<Object>> facts;
    private final Collection<MCMRule> rules;

    public MCMRelation(int arity, String name) {
        this.arity = arity;
        this.name = name;
        this.facts = new LinkedHashSet<>();
        this.rules = new LinkedHashSet<>();
    }

    public int getArity() {
        return arity;
    }

    public String getName() {
        return name;
    }

    public Collection<TupleN<Object>> getFacts() {
        return facts;
    }

    public Collection<MCMRule> getRules() {
        return rules;
    }

    public void addFact(final TupleN<Object> fact) {
        facts.add(fact);
    }

    public void addRule(final MCMRule rule) {
        rules.add(rule);
    }

    public void collectRelations(final Map<String, MCMRelation> relations) {
        if (!relations.containsKey(name)) {
            relations.put(name, this);
            for (MCMRule rule : getRules()) {
                rule.collectRelations(relations);
            }
        } else {
            if (!relations.get(name).equals(this))
                throw new RuntimeException("Different definitions for the relation " + name);
        }
    }

    @Override
    public String toString() {
        return "MCMRelation{" +
                "arity=" + arity +
                ", name='" + name + '\'' +
                ", facts=" + facts +
                ", rules=" + rules +
                '}';
    }
}
