/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.ic3;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public final class Cube {

    private final Set<Expr<BoolType>> literals;

    private Cube(final Collection<? extends Expr<BoolType>> literals) {
        this.literals = new HashSet<>(checkNotNull(literals));
    }

    public static Cube of(final Collection<? extends Expr<BoolType>> literals) {
        return new Cube(literals);
    }

    public Set<Expr<BoolType>> getLiterals() {
        return literals;
    }

    public Expr<BoolType> toExpr() {
        return And(literals);
    }

    /** Returns the clause ¬l₁ ∨ ¬l₂ ∨ … that is the negation of this cube. */
    public Clause negate() {
        return Clause.of(literals.stream().map(l -> Not(l)).collect(Collectors.toSet()));
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof Cube that)) return false;
        return literals.equals(that.literals);
    }

    @Override
    public int hashCode() {
        return literals.hashCode();
    }

    @Override
    public String toString() {
        return literals.toString();
    }
}
