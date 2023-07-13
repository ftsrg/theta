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

public class MCMConstraint {
    private final MCMRelation relation;
    private final ConstraintType constraintType;

    public MCMConstraint(MCMRelation relation, ConstraintType constraintType) {
        this.relation = relation;
        this.constraintType = constraintType;
    }

    public MCMRelation getRelation() {
        return relation;
    }

    public ConstraintType getConstraintType() {
        return constraintType;
    }

    public enum ConstraintType {
        EMPTY, NOTEMPTY,
        ACYCLIC, CYCLIC,
        IRREFLEXIVE, REFLEXIVE
    }

    @Override
    public String toString() {
        return "MCMConstraint{" +
                "relation=" + relation +
                ", constraintType=" + constraintType +
                '}';
    }
}
