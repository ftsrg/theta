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

package hu.bme.mit.theta.analysis.algorithm.mcm.mcm;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;

public class MCM {
    private final String name;
    private final Collection<MCMConstraint> constraints;
    private final Map<String, MCMRelation> relations;

    public MCM(String name) {
        this.name = name;
        constraints = new LinkedHashSet<>();
        relations = new LinkedHashMap<>();
    }

    public Collection<MCMConstraint> getConstraints() {
        return constraints;
    }

    public String getName() {
        return name;
    }

    public Map<String, MCMRelation> getRelations() {
        return relations;
    }

    public void addConstraint(final MCMConstraint constraint) {
        constraints.add(constraint);
        constraint.getRelation().collectRelations(relations);
    }


    @Override
    public String toString() {
        return "MCM{" +
                "name='" + name + '\'' +
                ", constraints=" + constraints +
                '}';
    }
}
