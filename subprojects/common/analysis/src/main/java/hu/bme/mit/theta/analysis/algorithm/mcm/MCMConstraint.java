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

import hu.bme.mit.theta.analysis.algorithm.mcm.rules.TransitiveClosure;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;

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

    public void encodeEvents(final List<Integer> idList, final EncodedRelationWrapper encodedRelationWrapper) {
        final EventConstantLookup baseRelation = relation.encodeEvents(idList, encodedRelationWrapper);
        final Expr<BoolType> expr = switch (constraintType) {
            case NOTEMPTY ->
                    Or(baseRelation.getConstants().stream().map(i -> i.getRef()).collect(Collectors.toList()));
            case EMPTY ->
                    Not(Or(baseRelation.getConstants().stream().map(i -> i.getRef()).collect(Collectors.toList())));
            case CYCLIC ->
                    Or(new MCMRelation(2, relation.getName() + "-acyclic", new TransitiveClosure(relation)).encodeEvents(idList, encodedRelationWrapper).getAll().entrySet().stream().filter(a -> Objects.equals(a.getKey().get(0), a.getKey().get(1))).map(i -> i.getValue().getRef()).collect(Collectors.toList()));
            case ACYCLIC ->
                    Not(Or(new MCMRelation(2, relation.getName() + "-acyclic", new TransitiveClosure(relation)).encodeEvents(idList, encodedRelationWrapper).getAll().entrySet().stream().filter(a -> Objects.equals(a.getKey().get(0), a.getKey().get(1))).map(i -> i.getValue().getRef()).collect(Collectors.toList())));
            case REFLEXIVE ->
                    Or(baseRelation.getAll().entrySet().stream().filter(a -> Objects.equals(a.getKey().get(0), a.getKey().get(1))).map(i -> i.getValue().getRef()).collect(Collectors.toList()));
            case IRREFLEXIVE ->
                    Not(Or(baseRelation.getAll().entrySet().stream().filter(a -> Objects.equals(a.getKey().get(0), a.getKey().get(1))).map(i -> i.getValue().getRef()).collect(Collectors.toList())));
        };
        encodedRelationWrapper.getSolver().add(expr);
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
